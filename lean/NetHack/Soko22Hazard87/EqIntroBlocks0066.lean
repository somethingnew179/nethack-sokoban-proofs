import NetHack.Soko22Hazard87.EqIntroBlocks0065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro16500 (p : Pattern) (selected : d18176 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18143 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16495 q selected
    | true =>
      simp only [d18143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16496 q selected
  have h2 (q : Pattern) (selected : d18144 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18145 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18151 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16496 q selected
    | true =>
      simp only [d18151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16497 q selected
  have h5 (q : Pattern) (selected : d18152 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18153 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18154 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18161 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16496 q selected
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
  have h9 (q : Pattern) (selected : d18162 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18163 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18171 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16499 q selected
  have h12 (q : Pattern) (selected : d18172 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18173 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18174 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18175 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18176 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16501 (p : Pattern) (selected : d18181 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18161 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16496 q selected
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
  have h2 (q : Pattern) (selected : d18162 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18163 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18171 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16499 q selected
  have h5 (q : Pattern) (selected : d18172 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18173 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18174 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18179 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18180 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18181 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16502 (p : Pattern) (selected : d18187 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18177 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16500 q selected
    | true =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18178 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16501 q selected
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18184 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18185 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18186 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18187 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16503 (p : Pattern) (selected : d18191 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1868 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
  have h2 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18188 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18189 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18190 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
  have h8 (q : Pattern) (selected : d10135 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18167 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18168 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18169 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18191 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16504 (p : Pattern) (selected : d18197 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18192 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
    | true =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16503 q selected
  have h2 (q : Pattern) (selected : d18193 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18194 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18195 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18196 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18197 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16505 (p : Pattern) (selected : d18203 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18182 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16501 q selected
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18183 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18198 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16504 q selected
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18199 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18200 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18201 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18202 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18203 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16506 (p : Pattern) (selected : d18215 p = 2) : d18142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1915 q = 2) : d1857 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
  have h2 (q : Pattern) (selected : d1726 q = 2) : d1555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
    | true =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1916 q = 2) : d1858 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18205 q = 2) : d18134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18205, d18134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18205, d18134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18206 q = 2) : d18135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18206, d18135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18206, d18135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17066 q = 2) : d17011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17066, d17011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17066, d17011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10618 q selected
  have h7 (q : Pattern) (selected : d10190 q = 2) : d10074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d10074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10618 q selected
    | true =>
      simp only [d10190, d10074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17067 q = 2) : d17012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17067, d17012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17067, d17012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18207 q = 2) : d18136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18207, d18136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18207, d18136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18208 q = 2) : d18137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18208, d18137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18208, d18137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18209 q = 2) : d18138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18209, d18138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18209, d18138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15450 q = 2) : d15387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10619 q selected
  have h13 (q : Pattern) (selected : d10200 q = 2) : d10063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10619 q selected
    | true =>
      simp only [d10200, d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15451 q = 2) : d15388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15451, d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18210 q = 2) : d18130 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18210, d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18210, d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18211 q = 2) : d18131 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18211, d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18211, d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15457 q = 2) : d15397 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
  have h18 (q : Pattern) (selected : d10215 q = 2) : d10085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
    | true =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15458 q = 2) : d15398 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18212 q = 2) : d18139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18212, d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18212, d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18213 q = 2) : d18140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18213, d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18213, d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18214 q = 2) : d18141 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18214, d18141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18214, d18141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18215 q = 2) : d18142 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18215, d18142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18215, d18142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16507 (p : Pattern) (selected : d18222 p = 2) : d18160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1919 q = 2) : d1862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
  have h2 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 2) : d1863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18216 q = 2) : d18155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18216, d18155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18216, d18155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18217 q = 2) : d18156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18217, d18156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18217, d18156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17073 q = 2) : d17027 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17073, d17027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17073, d17027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10622 q selected
  have h7 (q : Pattern) (selected : d10226 q = 2) : d10115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d10115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10622 q selected
    | true =>
      simp only [d10226, d10115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17074 q = 2) : d17028 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17074, d17028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17074, d17028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18218 q = 2) : d18157 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18218, d18157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18218, d18157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18219 q = 2) : d18158 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18219, d18158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18219, d18158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18220 q = 2) : d18159 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18220, d18159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18220, d18159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15457 q = 2) : d15397 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
  have h13 (q : Pattern) (selected : d10215 q = 2) : d10085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10620 q selected
    | true =>
      simp only [d10215, d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15458 q = 2) : d15398 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15458, d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18212 q = 2) : d18139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18212, d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18212, d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18213 q = 2) : d18140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18213, d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18213, d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18221 q = 2) : d18149 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18221, d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18221, d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18222 q = 2) : d18160 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18222, d18160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18222, d18160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16508 (p : Pattern) (selected : d18232 p = 2) : d18170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13535 q = 2) : d6496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
  have h2 (q : Pattern) (selected : d10243 q = 2) : d5134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
    | true =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 2) : d6497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18226 q = 2) : d18164 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18226, d18164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18226, d18164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18227 q = 2) : d18165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18227, d18165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18227, d18165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18228 q = 2) : d18166 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18228, d18166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18228, d18166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 2) : d15412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
  have h8 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 2) : d15413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18229 q = 2) : d18167 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18229, d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18229, d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18230 q = 2) : d18168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18230, d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18230, d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18231 q = 2) : d18169 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18231, d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18231, d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18232 q = 2) : d18170 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18232, d18170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18232, d18170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16509 (p : Pattern) (selected : d18240 p = 2) : d18191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1924 q = 2) : d1868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
  have h2 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 2) : d1869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18237 q = 2) : d18188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18237, d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18237, d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18238 q = 2) : d18189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18238, d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18238, d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18239 q = 2) : d18190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18239, d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18239, d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15466 q = 2) : d15412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
  have h8 (q : Pattern) (selected : d10255 q = 2) : d10135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10625 q selected
    | true =>
      simp only [d10255, d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15467 q = 2) : d15413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15467, d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18229 q = 2) : d18167 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18229, d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18229, d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18230 q = 2) : d18168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18230, d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18230, d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18231 q = 2) : d18169 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18231, d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18231, d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18240 q = 2) : d18191 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18240, d18191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18240, d18191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16510 (p : Pattern) (selected : d18246 p = 2) : d173599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18223 q = 2) : d18161 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18223, d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16506 q selected
    | true =>
      simp only [d18223, d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16507 q selected
  have h2 (q : Pattern) (selected : d18224 q = 2) : d18162 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18224, d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18224, d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18225 q = 2) : d18163 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18225, d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18225, d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18233 q = 2) : d18171 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18233, d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16507 q selected
    | true =>
      simp only [d18233, d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16508 q selected
  have h5 (q : Pattern) (selected : d18234 q = 2) : d18172 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18234, d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18234, d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18235 q = 2) : d18173 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18235, d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18235, d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18236 q = 2) : d18174 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18236, d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18236, d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18241 q = 2) : d18192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18241, d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16507 q selected
    | true =>
      simp only [d18241, d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16509 q selected
  have h9 (q : Pattern) (selected : d18242 q = 2) : d18193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18242, d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18242, d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18243 q = 2) : d18194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18243, d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18243, d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18244 q = 2) : d18195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18244, d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18244, d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18245 q = 2) : d173598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18245, d173598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18245, d173598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18246 q = 2) : d173599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18246, d173599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18246, d173599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16511 (p : Pattern) (selected : d18250 p = 2) : d18197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18241 q = 2) : d18192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18241, d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16507 q selected
    | true =>
      simp only [d18241, d18192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16509 q selected
  have h2 (q : Pattern) (selected : d18242 q = 2) : d18193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18242, d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18242, d18193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18243 q = 2) : d18194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18243, d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18243, d18194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18244 q = 2) : d18195 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18244, d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18244, d18195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18249 q = 2) : d18196 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18249, d18196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18249, d18196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18250 q = 2) : d18197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18250, d18197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18250, d18197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16512 (p : Pattern) (selected : d18256 p = 2) : d173605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18247 q = 2) : d173600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18247, d173600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16510 q selected
    | true =>
      simp only [d18247, d173600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18248 q = 2) : d173601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18248, d173601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18248, d173601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18251 q = 2) : d18198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18251, d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16511 q selected
    | true =>
      simp only [d18251, d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18252 q = 2) : d18199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18252, d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18252, d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18253 q = 2) : d173602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18253, d173602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18253, d173602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18254 q = 2) : d173603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18254, d173603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18254, d173603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18255 q = 2) : d173604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18255, d173604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18255, d173604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18256 q = 2) : d173605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18256, d173605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18256, d173605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16513 (p : Pattern) (selected : d18260 p = 2) : d18286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18251 q = 2) : d18198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18251, d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16511 q selected
    | true =>
      simp only [d18251, d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18252 q = 2) : d18199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18252, d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18252, d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18257 q = 2) : d18283 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18257, d18283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18257, d18283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18258 q = 2) : d18284 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18258, d18284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18258, d18284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18259 q = 2) : d18285 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18259, d18285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18259, d18285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18260 q = 2) : d18286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18260, d18286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18260, d18286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16514 (p : Pattern) (selected : d18263 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1868 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
  have h2 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18188 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18189 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18190 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18263 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16515 (p : Pattern) (selected : d18269 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18161 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16496 q selected
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
  have h2 (q : Pattern) (selected : d18162 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18163 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18171 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16499 q selected
  have h5 (q : Pattern) (selected : d18172 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18173 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18174 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18264 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16498 q selected
    | true =>
      simp only [d18264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16514 q selected
  have h9 (q : Pattern) (selected : d18265 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18266 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18267 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18268 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18269 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16516 (p : Pattern) (selected : d18275 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18270 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16515 q selected
    | true =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18271 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18272 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18273 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18274 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18275 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16517 (p : Pattern) (selected : d18281 p = 2) : d173611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18204 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16502 q selected
    | true =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16505 q selected
  have h2 (q : Pattern) (selected : d18261 q = 2) : d173606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18261, d173606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16512 q selected
    | true =>
      simp only [d18261, d173606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16513 q selected
  have h3 (q : Pattern) (selected : d18262 q = 2) : d173607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18262, d173607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18262, d173607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18276 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16516 q selected
    | true =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18277 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18278 q = 2) : d173608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18278, d173608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18278, d173608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18279 q = 2) : d173609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18279, d173609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18279, d173609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18280 q = 2) : d173610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18280, d173610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18280, d173610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18281 q = 2) : d173611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18281, d173611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18281, d173611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16518 (p : Pattern) (selected : d18286 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18198 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16504 q selected
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18199 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18283 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18284 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18285 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18286 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16519 (p : Pattern) (selected : d18292 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18287 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16518 q selected
    | true =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18288 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18289 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18290 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18291 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18292 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16520 (p : Pattern) (selected : d18298 p = 2) : d173617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18282 q = 2) : d173612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18282, d173612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18282, d173612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16517 q selected
  have h2 (q : Pattern) (selected : d18293 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16519 q selected
  have h3 (q : Pattern) (selected : d18294 q = 2) : d173613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18294, d173613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18294, d173613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18295 q = 2) : d173614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18295, d173614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18295, d173614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18296 q = 2) : d173615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18296, d173615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18296, d173615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18297 q = 2) : d173616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18297, d173616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18297, d173616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18298 q = 2) : d173617 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18298, d173617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18298, d173617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16521 (p : Pattern) (selected : d18304 p = 2) : d173623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18299 q = 2) : d173618 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18299, d173618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18299, d173618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16520 q selected
  have h2 (q : Pattern) (selected : d18300 q = 2) : d173619 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18300, d173619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18300, d173619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18301 q = 2) : d173620 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18301, d173620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18301, d173620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18302 q = 2) : d173621 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18302, d173621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18302, d173621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18303 q = 2) : d173622 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d18303, d173622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18303, d173622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18304 q = 2) : d173623 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d18304, d173623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18304, d173623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16522 (p : Pattern) (selected : d18317 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2331 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
  have h2 (q : Pattern) (selected : d2144 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2332 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18309 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18310 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17369 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10640 q selected
  have h7 (q : Pattern) (selected : d10343 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10640 q selected
    | true =>
      simp only [d10343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17370 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18311 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18312 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18313 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h13 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18314 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18315 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18316 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d18317 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16523 (p : Pattern) (selected : d18326 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2335 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
  have h2 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18318 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18319 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17376 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10643 q selected
  have h7 (q : Pattern) (selected : d10364 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10643 q selected
    | true =>
      simp only [d10364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17377 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18320 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18321 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18322 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h13 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18314 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18315 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15775 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
  have h18 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15776 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18323 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18324 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18325 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18326 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16524 (p : Pattern) (selected : d18331 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h2 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18314 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18315 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15775 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
  have h7 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15776 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18323 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18324 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18325 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18330 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18331 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16525 (p : Pattern) (selected : d18341 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2340 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
  have h2 (q : Pattern) (selected : d2053 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2341 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18336 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18337 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10647 q selected
  have h7 (q : Pattern) (selected : d10391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10647 q selected
    | true =>
      simp only [d10391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18338 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18339 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18340 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15775 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
  have h13 (q : Pattern) (selected : d10371 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10644 q selected
    | true =>
      simp only [d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15776 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18323 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18324 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18330 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18341 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16526 (p : Pattern) (selected : d18351 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6643 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3872 q selected
  have h2 (q : Pattern) (selected : d5247 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3872 q selected
    | true =>
      simp only [d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6644 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18345 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18346 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18347 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15790 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
  have h8 (q : Pattern) (selected : d10412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15791 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18350 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18351 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16527 (p : Pattern) (selected : d18357 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18327 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16522 q selected
    | true =>
      simp only [d18327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16523 q selected
  have h2 (q : Pattern) (selected : d18328 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18329 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18332 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16523 q selected
    | true =>
      simp only [d18332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16524 q selected
  have h5 (q : Pattern) (selected : d18333 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18334 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18335 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18342 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16523 q selected
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
  have h9 (q : Pattern) (selected : d18343 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18344 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18352 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16526 q selected
  have h12 (q : Pattern) (selected : d18353 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18354 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18355 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18356 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18357 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16528 (p : Pattern) (selected : d18362 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18342 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16523 q selected
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
  have h2 (q : Pattern) (selected : d18343 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18344 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18352 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16526 q selected
  have h5 (q : Pattern) (selected : d18353 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18354 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18355 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18360 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18361 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18362 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16529 (p : Pattern) (selected : d18368 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18358 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16527 q selected
    | true =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18359 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18363 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16528 q selected
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18364 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18365 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18366 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18367 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18368 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16530 (p : Pattern) (selected : d18372 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2346 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
  have h2 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18369 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18370 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18371 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15790 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
  have h8 (q : Pattern) (selected : d10412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10649 q selected
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15791 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18350 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18372 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16531 (p : Pattern) (selected : d18378 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18373 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
    | true =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16530 q selected
  have h2 (q : Pattern) (selected : d18374 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18375 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18376 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18377 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18378 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16532 (p : Pattern) (selected : d18384 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18363 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16528 q selected
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18364 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18379 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16531 q selected
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18380 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18381 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18382 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18383 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18384 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16533 (p : Pattern) (selected : d18396 p = 2) : d18326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2393 q = 2) : d2335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
  have h2 (q : Pattern) (selected : d2201 q = 2) : d2035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
    | true =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2394 q = 2) : d2336 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18386 q = 2) : d18318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18386, d18318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18386, d18318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18387 q = 2) : d18319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18387, d18319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18387, d18319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17430 q = 2) : d17376 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17430, d17376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17430, d17376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10657 q selected
  have h7 (q : Pattern) (selected : d10458 q = 2) : d10364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d10364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10657 q selected
    | true =>
      simp only [d10458, d10364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17431 q = 2) : d17377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17431, d17377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17431, d17377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18388 q = 2) : d18320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18388, d18320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18388, d18320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18389 q = 2) : d18321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18389, d18321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18389, d18321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18390 q = 2) : d18322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18390, d18322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18390, d18322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15828 q = 2) : d13813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10658 q selected
  have h13 (q : Pattern) (selected : d10468 q = 2) : d10353 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10658 q selected
    | true =>
      simp only [d10468, d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15829 q = 2) : d13814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15829, d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18391 q = 2) : d18314 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18391, d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18391, d18314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18392 q = 2) : d18315 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18392, d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18392, d18315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15835 q = 2) : d15775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
  have h18 (q : Pattern) (selected : d10482 q = 2) : d10371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
    | true =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15836 q = 2) : d15776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18393 q = 2) : d18323 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18393, d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18393, d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18394 q = 2) : d18324 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18394, d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18394, d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18395 q = 2) : d18325 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18395, d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18395, d18325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18396 q = 2) : d18326 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18396, d18326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18396, d18326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16534 (p : Pattern) (selected : d18403 p = 2) : d18341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2397 q = 2) : d2340 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
  have h2 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 2) : d2341 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18397 q = 2) : d18336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18397, d18336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18397, d18336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18398 q = 2) : d18337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18398, d18337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18398, d18337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17437 q = 2) : d17391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17437, d17391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17437, d17391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10661 q selected
  have h7 (q : Pattern) (selected : d10493 q = 2) : d10391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d10391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10661 q selected
    | true =>
      simp only [d10493, d10391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17438 q = 2) : d17392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17438, d17392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17438, d17392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18399 q = 2) : d18338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18399, d18338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18399, d18338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18400 q = 2) : d18339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18400, d18339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18400, d18339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18401 q = 2) : d18340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18401, d18340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18401, d18340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15835 q = 2) : d15775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d15775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
  have h13 (q : Pattern) (selected : d10482 q = 2) : d10371 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10659 q selected
    | true =>
      simp only [d10482, d10371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15836 q = 2) : d15776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15836, d15776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18393 q = 2) : d18323 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18393, d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18393, d18323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18394 q = 2) : d18324 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18394, d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18394, d18324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18402 q = 2) : d18330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18402, d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18402, d18330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18403 q = 2) : d18341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18403, d18341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18403, d18341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16535 (p : Pattern) (selected : d18413 p = 2) : d18351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13862 q = 2) : d6643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
  have h2 (q : Pattern) (selected : d10508 q = 2) : d5247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
    | true =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13863 q = 2) : d6644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18407 q = 2) : d18345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18407, d18345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18407, d18345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18408 q = 2) : d18346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18408, d18346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18408, d18346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18409 q = 2) : d18347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18409, d18347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18409, d18347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 2) : d15790 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
  have h8 (q : Pattern) (selected : d10521 q = 2) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
    | true =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 2) : d15791 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18410 q = 2) : d18348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18410, d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18410, d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18411 q = 2) : d18349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18411, d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18411, d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18412 q = 2) : d18350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18412, d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18412, d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18413 q = 2) : d18351 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18413, d18351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18413, d18351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16536 (p : Pattern) (selected : d18421 p = 2) : d18372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2402 q = 2) : d2346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
  have h2 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 2) : d2347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18418 q = 2) : d18369 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18418, d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18418, d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18419 q = 2) : d18370 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18419, d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18419, d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18420 q = 2) : d18371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18420, d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18420, d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15844 q = 2) : d15790 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d15790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
  have h8 (q : Pattern) (selected : d10521 q = 2) : d10412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10664 q selected
    | true =>
      simp only [d10521, d10412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15845 q = 2) : d15791 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15845, d15791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18410 q = 2) : d18348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18410, d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18410, d18348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18411 q = 2) : d18349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18411, d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18411, d18349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18412 q = 2) : d18350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18412, d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18412, d18350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18421 q = 2) : d18372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18421, d18372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18421, d18372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16537 (p : Pattern) (selected : d18427 p = 2) : d173629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18404 q = 2) : d18342 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18404, d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16533 q selected
    | true =>
      simp only [d18404, d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16534 q selected
  have h2 (q : Pattern) (selected : d18405 q = 2) : d18343 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18405, d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18405, d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18406 q = 2) : d18344 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18406, d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18406, d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18414 q = 2) : d18352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18414, d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16534 q selected
    | true =>
      simp only [d18414, d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16535 q selected
  have h5 (q : Pattern) (selected : d18415 q = 2) : d18353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18415, d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18415, d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18416 q = 2) : d18354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18416, d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18416, d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18417 q = 2) : d18355 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18417, d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18417, d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18422 q = 2) : d18373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18422, d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16534 q selected
    | true =>
      simp only [d18422, d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16536 q selected
  have h9 (q : Pattern) (selected : d18423 q = 2) : d18374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18423, d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18423, d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18424 q = 2) : d18375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18424, d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18424, d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18425 q = 2) : d18376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18425, d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18425, d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18426 q = 2) : d173628 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18426, d173628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18426, d173628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18427 q = 2) : d173629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18427, d173629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18427, d173629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16538 (p : Pattern) (selected : d18431 p = 2) : d18378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18422 q = 2) : d18373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18422, d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16534 q selected
    | true =>
      simp only [d18422, d18373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16536 q selected
  have h2 (q : Pattern) (selected : d18423 q = 2) : d18374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18423, d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18423, d18374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18424 q = 2) : d18375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18424, d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18424, d18375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18425 q = 2) : d18376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18425, d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18425, d18376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18430 q = 2) : d18377 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18430, d18377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18430, d18377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18431 q = 2) : d18378 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18431, d18378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18431, d18378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16539 (p : Pattern) (selected : d18437 p = 2) : d173635 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18428 q = 2) : d173630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18428, d173630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16537 q selected
    | true =>
      simp only [d18428, d173630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18429 q = 2) : d173631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18429, d173631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18429, d173631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18432 q = 2) : d18379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18432, d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16538 q selected
    | true =>
      simp only [d18432, d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18433 q = 2) : d18380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18433, d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18433, d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18434 q = 2) : d173632 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18434, d173632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18434, d173632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18435 q = 2) : d173633 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18435, d173633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18435, d173633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18436 q = 2) : d173634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18436, d173634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18436, d173634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18437 q = 2) : d173635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18437, d173635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18437, d173635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16540 (p : Pattern) (selected : d18441 p = 2) : d18467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18432 q = 2) : d18379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18432, d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16538 q selected
    | true =>
      simp only [d18432, d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18433 q = 2) : d18380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18433, d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18433, d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18438 q = 2) : d18464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18438, d18464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18438, d18464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18439 q = 2) : d18465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18439, d18465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18439, d18465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18440 q = 2) : d18466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18440, d18466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18440, d18466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18441 q = 2) : d18467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18441, d18467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18441, d18467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16541 (p : Pattern) (selected : d18444 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2346 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
  have h2 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18369 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18370 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18371 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18444 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16542 (p : Pattern) (selected : d18450 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18342 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16523 q selected
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
  have h2 (q : Pattern) (selected : d18343 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18344 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18352 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16526 q selected
  have h5 (q : Pattern) (selected : d18353 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18354 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18355 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18445 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16525 q selected
    | true =>
      simp only [d18445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16541 q selected
  have h9 (q : Pattern) (selected : d18446 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18447 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18448 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18449 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18450 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16543 (p : Pattern) (selected : d18456 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18451 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16542 q selected
    | true =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18452 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18453 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18454 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18455 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18456 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16544 (p : Pattern) (selected : d18462 p = 2) : d173641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18385 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16529 q selected
    | true =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16532 q selected
  have h2 (q : Pattern) (selected : d18442 q = 2) : d173636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18442, d173636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16539 q selected
    | true =>
      simp only [d18442, d173636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16540 q selected
  have h3 (q : Pattern) (selected : d18443 q = 2) : d173637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18443, d173637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18443, d173637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18457 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16543 q selected
    | true =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18458 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18459 q = 2) : d173638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18459, d173638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18459, d173638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18460 q = 2) : d173639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18460, d173639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18460, d173639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18461 q = 2) : d173640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18461, d173640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18461, d173640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18462 q = 2) : d173641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18462, d173641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18462, d173641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16545 (p : Pattern) (selected : d18467 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18379 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16531 q selected
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18380 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18464 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18465 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18466 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18467 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16546 (p : Pattern) (selected : d18473 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18468 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16545 q selected
    | true =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18469 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18470 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18471 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18472 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18473 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16547 (p : Pattern) (selected : d18479 p = 2) : d173647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18463 q = 2) : d173642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18463, d173642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18463, d173642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16544 q selected
  have h2 (q : Pattern) (selected : d18474 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16546 q selected
  have h3 (q : Pattern) (selected : d18475 q = 2) : d173643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18475, d173643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18475, d173643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18476 q = 2) : d173644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18476, d173644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18476, d173644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18477 q = 2) : d173645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18477, d173645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18477, d173645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18478 q = 2) : d173646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18478, d173646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18478, d173646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18479 q = 2) : d173647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18479, d173647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18479, d173647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16548 (p : Pattern) (selected : d18485 p = 2) : d173653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18480 q = 2) : d173648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18480, d173648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18480, d173648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16547 q selected
  have h2 (q : Pattern) (selected : d18481 q = 2) : d173649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18481, d173649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18481, d173649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18482 q = 2) : d173650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18482, d173650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18482, d173650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18483 q = 2) : d173651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18483, d173651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18483, d173651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18484 q = 2) : d173652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d18484, d173652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18484, d173652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18485 q = 2) : d173653 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d18485, d173653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18485, d173653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16549 (p : Pattern) (selected : d18491 p = 2) : d173659 p = 1 := by
  have h0 (q : Pattern) (selected : d17811 q = 2) : d173548 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d17811, d173548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16426 q selected
    | true =>
      simp only [d17811, d173548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16444 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d17940 q = 2) : d173567 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d17940, d173567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17940, d173567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16467 q selected
  have h3 (q : Pattern) (selected : d17941 q = 2) : d173568 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d17941, d173568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17941, d173568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18120 q = 2) : d173595 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d18120, d173595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18120, d173595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16494 q selected
  have h5 (q : Pattern) (selected : d18121 q = 2) : d173596 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d18121, d173596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18121, d173596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18122 q = 2) : d173597 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d18122, d173597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18122, d173597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18305 q = 2) : d173624 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d18305, d173624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18305, d173624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16521 q selected
  have h8 (q : Pattern) (selected : d18306 q = 2) : d173625 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d18306, d173625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18306, d173625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18307 q = 2) : d173626 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d18307, d173626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18307, d173626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18308 q = 2) : d173627 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d18308, d173627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18308, d173627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18486 q = 2) : d173654 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d18486, d173654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18486, d173654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16548 q selected
  have h12 (q : Pattern) (selected : d18487 q = 2) : d173655 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d18487, d173655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18487, d173655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18488 q = 2) : d173656 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d18488, d173656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18488, d173656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18489 q = 2) : d173657 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d18489, d173657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18489, d173657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18490 q = 2) : d173658 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d18490, d173658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18490, d173658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18491 q = 2) : d173659 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d18491, d173659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18491, d173659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16550 (p : Pattern) (selected : d18497 p = 2) : d173665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18492 q = 2) : d173660 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d18492, d173660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16549 q selected
    | true =>
      simp only [d18492, d173660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18493 q = 2) : d173661 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d18493, d173661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18493, d173661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18494 q = 2) : d173662 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d18494, d173662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18494, d173662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18495 q = 2) : d173663 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d18495, d173663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18495, d173663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18496 q = 2) : d173664 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d18496, d173664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18496, d173664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18497 q = 2) : d173665 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d18497, d173665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18497, d173665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16551 (p : Pattern) (selected : d18503 p = 2) : d173671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18498 q = 2) : d173666 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d18498, d173666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16550 q selected
    | true =>
      simp only [d18498, d173666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18499 q = 2) : d173667 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d18499, d173667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18499, d173667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18500 q = 2) : d173668 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d18500, d173668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18500, d173668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18501 q = 2) : d173669 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d18501, d173669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18501, d173669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18502 q = 2) : d173670 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d18502, d173670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18502, d173670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18503 q = 2) : d173671 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d18503, d173671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18503, d173671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16552 (p : Pattern) (selected : d18509 p = 2) : d173677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18504 q = 2) : d173672 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d18504, d173672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16551 q selected
    | true =>
      simp only [d18504, d173672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18505 q = 2) : d173673 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d18505, d173673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18505, d173673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18506 q = 2) : d173674 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d18506, d173674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18506, d173674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18507 q = 2) : d173675 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d18507, d173675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18507, d173675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18508 q = 2) : d173676 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d18508, d173676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18508, d173676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18509 q = 2) : d173677 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d18509, d173677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18509, d173677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16553 (p : Pattern) (selected : d18515 p = 2) : d173683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18510 q = 2) : d173678 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d18510, d173678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16552 q selected
    | true =>
      simp only [d18510, d173678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18511 q = 2) : d173679 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d18511, d173679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18511, d173679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18512 q = 2) : d173680 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d18512, d173680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18512, d173680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18513 q = 2) : d173681 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d18513, d173681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18513, d173681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18514 q = 2) : d173682 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d18514, d173682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18514, d173682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18515 q = 2) : d173683 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d18515, d173683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18515, d173683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16554 (p : Pattern) (selected : d18521 p = 2) : d173689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18516 q = 2) : d173684 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d18516, d173684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16553 q selected
    | true =>
      simp only [d18516, d173684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18517 q = 2) : d173685 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d18517, d173685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18517, d173685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18518 q = 2) : d173686 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d18518, d173686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18518, d173686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18519 q = 2) : d173687 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d18519, d173687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18519, d173687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18520 q = 2) : d173688 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d18520, d173688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18520, d173688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18521 q = 2) : d173689 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d18521, d173689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18521, d173689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16555 (p : Pattern) (selected : d18527 p = 2) : d173695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18522 q = 2) : d173690 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d18522, d173690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16554 q selected
    | true =>
      simp only [d18522, d173690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18523 q = 2) : d173691 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d18523, d173691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18523, d173691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18524 q = 2) : d173692 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d18524, d173692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18524, d173692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18525 q = 2) : d173693 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d18525, d173693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18525, d173693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18526 q = 2) : d173694 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d18526, d173694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18526, d173694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18527 q = 2) : d173695 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d18527, d173695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18527, d173695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16556 (p : Pattern) (selected : d18533 p = 2) : d173701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18528 q = 2) : d173696 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d18528, d173696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16555 q selected
    | true =>
      simp only [d18528, d173696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18529 q = 2) : d173697 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d18529, d173697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18529, d173697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18530 q = 2) : d173698 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d18530, d173698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18530, d173698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18531 q = 2) : d173699 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d18531, d173699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18531, d173699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18532 q = 2) : d173700 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d18532, d173700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18532, d173700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18533 q = 2) : d173701 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d18533, d173701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18533, d173701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16557 (p : Pattern) (selected : d181870 p = 0) : d182843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181867 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181868 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181869 q = 0) : d182842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181870 q = 0) : d182843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181870, d182843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181870, d182843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16558 (p : Pattern) (selected : d181876 p = 0) : d182849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181871 q = 0) : d182844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
    | true =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181872 q = 0) : d182845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181873 q = 0) : d182846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181874 q = 0) : d182847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181874, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181874, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181875 q = 0) : d182848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181875, d182848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181875, d182848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181876 q = 0) : d182849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181876, d182849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181876, d182849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16559 (p : Pattern) (selected : d181882 p = 0) : d182855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181877 q = 0) : d182850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181877, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16558 q selected
    | true =>
      simp only [d181877, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181878 q = 0) : d182851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181878, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181878, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181879 q = 0) : d182852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181879, d182852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181879, d182852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181880 q = 0) : d182853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181880, d182853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181880, d182853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181881 q = 0) : d182854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181881, d182854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181881, d182854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181882 q = 0) : d182855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181882, d182855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181882, d182855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16560 (p : Pattern) (selected : d181888 p = 0) : d182861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181883 q = 0) : d182856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16559 q selected
    | true =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181884 q = 0) : d182857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181884, d182857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181884, d182857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181885 q = 0) : d182858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181885, d182858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181885, d182858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181886 q = 0) : d182859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181886, d182859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181886, d182859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181887 q = 0) : d182860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181887, d182860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181887, d182860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181888 q = 0) : d182861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181888, d182861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181888, d182861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16561 (p : Pattern) (selected : d181894 p = 0) : d182867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181889 q = 0) : d182862 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181889, d182862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181889, d182862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16560 q selected
  have h2 (q : Pattern) (selected : d181890 q = 0) : d182863 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181890, d182863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181890, d182863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181891 q = 0) : d182864 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181891, d182864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181891, d182864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181892 q = 0) : d182865 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181892, d182865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181892, d182865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181893 q = 0) : d182866 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181893, d182866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181893, d182866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181894 q = 0) : d182867 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181894, d182867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181894, d182867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16562 (p : Pattern) (selected : d181902 p = 0) : d182875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181899 q = 0) : d182872 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181899, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d181899, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181900 q = 0) : d182873 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181900, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181900, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181867 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181868 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181901 q = 0) : d182874 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181901, d182874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181901, d182874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181869 q = 0) : d182842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181902 q = 0) : d182875 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181902, d182875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181902, d182875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16563 (p : Pattern) (selected : d181908 p = 0) : d182881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181903 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
    | true =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
  have h2 (q : Pattern) (selected : d181904 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181905 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181871 q = 0) : d182844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
    | true =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181872 q = 0) : d182845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181873 q = 0) : d182846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181906 q = 0) : d182879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181906, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181906, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181874 q = 0) : d182847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181874, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181874, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181907 q = 0) : d182880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181907, d182880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181907, d182880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d181908 q = 0) : d182881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181908, d182881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d181908, d182881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16564 (p : Pattern) (selected : d181914 p = 0) : d182887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181909 q = 0) : d182882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16563 q selected
    | true =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181910 q = 0) : d182883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181877 q = 0) : d182850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181877, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16558 q selected
    | true =>
      simp only [d181877, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181878 q = 0) : d182851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181878, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181878, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181911 q = 0) : d182884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181911, d182884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181911, d182884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181912 q = 0) : d182885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181912, d182885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181912, d182885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181913 q = 0) : d182886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181913, d182886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181913, d182886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181914 q = 0) : d182887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181914, d182887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181914, d182887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16565 (p : Pattern) (selected : d181919 p = 0) : d182843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181916 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181917 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181918 q = 0) : d182842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181918, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181918, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181919 q = 0) : d182843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181919, d182843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181919, d182843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16566 (p : Pattern) (selected : d181925 p = 0) : d182849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181920 q = 0) : d182844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181920, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16565 q selected
    | true =>
      simp only [d181920, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181921 q = 0) : d182845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181921, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181921, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181922 q = 0) : d182846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181922, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181922, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181923 q = 0) : d182847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181923, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181923, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181924 q = 0) : d182848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181924, d182848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181924, d182848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181925 q = 0) : d182849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181925, d182849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181925, d182849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16567 (p : Pattern) (selected : d181931 p = 0) : d182855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181926 q = 0) : d182850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181926, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16566 q selected
    | true =>
      simp only [d181926, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181927 q = 0) : d182851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181927, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181927, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181928 q = 0) : d182852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181928, d182852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181928, d182852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181929 q = 0) : d182853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181929, d182853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181929, d182853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181930 q = 0) : d182854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181930, d182854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181930, d182854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181931 q = 0) : d182855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181931, d182855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181931, d182855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16568 (p : Pattern) (selected : d181937 p = 0) : d182893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181915 q = 0) : d182888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181915, d182888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16564 q selected
    | true =>
      simp only [d181915, d182888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16559 q selected
  have h2 (q : Pattern) (selected : d181932 q = 0) : d182856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181932, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16567 q selected
    | true =>
      simp only [d181932, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181933 q = 0) : d182889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181933, d182889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181933, d182889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181883 q = 0) : d182856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16559 q selected
    | true =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181884 q = 0) : d182857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181884, d182857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181884, d182857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181934 q = 0) : d182890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181934, d182890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181934, d182890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181935 q = 0) : d182891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181935, d182891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181935, d182891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181936 q = 0) : d182892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181936, d182892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181936, d182892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d181937 q = 0) : d182893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181937, d182893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181937, d182893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16569 (p : Pattern) (selected : d181943 p = 0) : d182899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181938 q = 0) : d182894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181938, d182894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181938, d182894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16568 q selected
  have h2 (q : Pattern) (selected : d181939 q = 0) : d182895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181939, d182895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181939, d182895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181940 q = 0) : d182896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181940, d182896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181940, d182896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181941 q = 0) : d182897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181941, d182897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181941, d182897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181942 q = 0) : d182898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181942, d182898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181942, d182898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181943 q = 0) : d182899 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181943, d182899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181943, d182899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16570 (p : Pattern) (selected : d181955 p = 0) : d182911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181949 q = 0) : d182905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181949, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d181949, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181950 q = 0) : d182906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181950, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181950, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181899 q = 0) : d182872 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181899, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d181899, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181900 q = 0) : d182873 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181900, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181900, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181951 q = 0) : d182907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181951, d182907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181951, d182907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181952 q = 0) : d182908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181953 q = 0) : d182909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181867 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181868 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d181954 q = 0) : d182910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181954, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181954, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d181955 q = 0) : d182911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181955, d182911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181955, d182911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16571 (p : Pattern) (selected : d181961 p = 0) : d182917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181956 q = 0) : d182912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16570 q selected
    | true =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
  have h2 (q : Pattern) (selected : d181957 q = 0) : d182913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181958 q = 0) : d182914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181903 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
    | true =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
  have h5 (q : Pattern) (selected : d181904 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181905 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181959 q = 0) : d182915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181871 q = 0) : d182844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
    | true =>
      simp only [d181871, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181872 q = 0) : d182845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181872, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d181873 q = 0) : d182846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181873, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d181906 q = 0) : d182879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181906, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181906, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d181960 q = 0) : d182916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181960, d182916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181960, d182916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d181961 q = 0) : d182917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181961, d182917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d181961, d182917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16572 (p : Pattern) (selected : d181967 p = 0) : d182923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181962 q = 0) : d182918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181962, d182918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16571 q selected
    | true =>
      simp only [d181962, d182918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181963 q = 0) : d182919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181963, d182919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181963, d182919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181909 q = 0) : d182882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16563 q selected
    | true =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181910 q = 0) : d182883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181964 q = 0) : d182920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181964, d182920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181964, d182920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181965 q = 0) : d182921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181965, d182921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181965, d182921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181966 q = 0) : d182922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181966, d182922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181966, d182922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181967 q = 0) : d182923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181967, d182923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181967, d182923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16573 (p : Pattern) (selected : d181972 p = 0) : d182875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181969 q = 0) : d182872 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181969, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d181969, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181970 q = 0) : d182873 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181970, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181970, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181916 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181917 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181971 q = 0) : d182874 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181971, d182874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181971, d182874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181918 q = 0) : d182842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181918, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181918, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181972 q = 0) : d182875 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181972, d182875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181972, d182875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16574 (p : Pattern) (selected : d181978 p = 0) : d182881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181973 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16573 q selected
    | true =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16565 q selected
  have h2 (q : Pattern) (selected : d181974 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181975 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181920 q = 0) : d182844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181920, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16565 q selected
    | true =>
      simp only [d181920, d182844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181921 q = 0) : d182845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181921, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181921, d182845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181922 q = 0) : d182846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181922, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181922, d182846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181976 q = 0) : d182879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181976, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181976, d182879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181923 q = 0) : d182847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181923, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181923, d182847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181977 q = 0) : d182880 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181977, d182880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181977, d182880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d181978 q = 0) : d182881 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181978, d182881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d181978, d182881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16575 (p : Pattern) (selected : d181984 p = 0) : d182887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181979 q = 0) : d182882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181979, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16574 q selected
    | true =>
      simp only [d181979, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181980 q = 0) : d182883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181980, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181980, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181926 q = 0) : d182850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181926, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16566 q selected
    | true =>
      simp only [d181926, d182850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181927 q = 0) : d182851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181927, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181927, d182851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181981 q = 0) : d182884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181981, d182884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181981, d182884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181982 q = 0) : d182885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181982, d182885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181982, d182885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181983 q = 0) : d182886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181983, d182886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181983, d182886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181984 q = 0) : d182887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181984, d182887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181984, d182887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16576 (p : Pattern) (selected : d181990 p = 0) : d182929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181909 q = 0) : d182882 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16563 q selected
    | true =>
      simp only [d181909, d182882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181910 q = 0) : d182883 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181910, d182883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181987 q = 0) : d182926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181987, d182926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181987, d182926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181988 q = 0) : d182927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181988, d182927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181988, d182927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181989 q = 0) : d182928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181989, d182928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181989, d182928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181990 q = 0) : d182929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181990, d182929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181990, d182929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16577 (p : Pattern) (selected : d181996 p = 0) : d182935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181968 q = 0) : d182924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181968, d182924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16572 q selected
    | true =>
      simp only [d181968, d182924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16564 q selected
  have h2 (q : Pattern) (selected : d181985 q = 0) : d182888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181985, d182888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16575 q selected
    | true =>
      simp only [d181985, d182888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16567 q selected
  have h3 (q : Pattern) (selected : d181986 q = 0) : d182925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181986, d182925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181986, d182925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181991 q = 0) : d182930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181991, d182930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16576 q selected
    | true =>
      simp only [d181991, d182930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181992 q = 0) : d182931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181992, d182931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181992, d182931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181993 q = 0) : d182932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181993, d182932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181993, d182932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181994 q = 0) : d182933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181994, d182933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181994, d182933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181995 q = 0) : d182934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181995, d182934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181995, d182934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d181996 q = 0) : d182935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181996, d182935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181996, d182935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16578 (p : Pattern) (selected : d182002 p = 0) : d182941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181883 q = 0) : d182856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16559 q selected
    | true =>
      simp only [d181883, d182856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181998 q = 0) : d182937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181998, d182937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181998, d182937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181999 q = 0) : d182938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181999, d182938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181999, d182938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182000 q = 0) : d182939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182000, d182939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182000, d182939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182001 q = 0) : d182940 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182001, d182940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182001, d182940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182002 q = 0) : d182941 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182002, d182941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182002, d182941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16579 (p : Pattern) (selected : d182008 p = 0) : d182947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181997 q = 0) : d182936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181997, d182936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181997, d182936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16577 q selected
  have h2 (q : Pattern) (selected : d182003 q = 0) : d182942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182003, d182942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182003, d182942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16578 q selected
  have h3 (q : Pattern) (selected : d182004 q = 0) : d182943 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182004, d182943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182004, d182943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182005 q = 0) : d182944 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182005, d182944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182005, d182944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182006 q = 0) : d182945 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182006, d182945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182006, d182945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182007 q = 0) : d182946 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182007, d182946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182007, d182946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182008 q = 0) : d182947 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182008, d182947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182008, d182947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16580 (p : Pattern) (selected : d182014 p = 0) : d182953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181895 q = 0) : d182868 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181895, d182868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181895, d182868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16561 q selected
  have h2 (q : Pattern) (selected : d181896 q = 0) : d182869 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181896, d182869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181896, d182869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181897 q = 0) : d182870 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181897, d182870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181897, d182870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181898 q = 0) : d182871 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181898, d182871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181898, d182871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181944 q = 0) : d182900 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181944, d182900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181944, d182900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16569 q selected
  have h6 (q : Pattern) (selected : d181945 q = 0) : d182901 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181945, d182901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181945, d182901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181946 q = 0) : d182902 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181946, d182902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181946, d182902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181947 q = 0) : d182903 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181947, d182903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181947, d182903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d181948 q = 0) : d182904 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181948, d182904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181948, d182904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182009 q = 0) : d182948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182009, d182948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182009, d182948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16579 q selected
  have h11 (q : Pattern) (selected : d182010 q = 0) : d182949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182010, d182949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182010, d182949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d182011 q = 0) : d182950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182011, d182950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182011, d182950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182012 q = 0) : d182951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182012, d182951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182012, d182951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182013 q = 0) : d182952 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182013, d182952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182013, d182952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182014 q = 0) : d182953 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182014, d182953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182014, d182953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro16581 (p : Pattern) (selected : d182023 p = 0) : d182962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182015 q = 0) : d182954 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182015, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d182015, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182016 q = 0) : d182955 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182016, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182016, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182017 q = 0) : d182956 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182017, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d182017, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182018 q = 0) : d182957 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182018, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182018, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182019 q = 0) : d182958 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182019, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182019, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182020 q = 0) : d182959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182021 q = 0) : d182960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181952 q = 0) : d182908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181953 q = 0) : d182909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182022 q = 0) : d182961 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182022, d182961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182022, d182961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182023 q = 0) : d182962 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182023, d182962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182023, d182962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16582 (p : Pattern) (selected : d182027 p = 0) : d182966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181952 q = 0) : d182908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d181952, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181953 q = 0) : d182909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181953, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181867 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d181867, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181868 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181868, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181954 q = 0) : d182910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181954, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181954, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181869 q = 0) : d182842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181869, d182842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182027 q = 0) : d182966 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182027, d182966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182027, d182966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16583 (p : Pattern) (selected : d182033 p = 0) : d182972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182024 q = 0) : d182963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182024, d182963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16581 q selected
    | true =>
      simp only [d182024, d182963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16570 q selected
  have h2 (q : Pattern) (selected : d182025 q = 0) : d182964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182025, d182964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182025, d182964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182026 q = 0) : d182965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182026, d182965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182026, d182965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182028 q = 0) : d182967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182028, d182967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16570 q selected
    | true =>
      simp only [d182028, d182967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16582 q selected
  have h5 (q : Pattern) (selected : d182029 q = 0) : d182968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182029, d182968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182029, d182968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182030 q = 0) : d182969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182030, d182969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182030, d182969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182031 q = 0) : d182970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182031, d182970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182031, d182970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181956 q = 0) : d182912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16570 q selected
    | true =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
  have h9 (q : Pattern) (selected : d181957 q = 0) : d182913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d181958 q = 0) : d182914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d181903 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
    | true =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
  have h12 (q : Pattern) (selected : d181904 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d181905 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d181959 q = 0) : d182915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182032 q = 0) : d182971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182032, d182971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182032, d182971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182033 q = 0) : d182972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182033, d182972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182033, d182972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16584 (p : Pattern) (selected : d182038 p = 0) : d182977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181956 q = 0) : d182912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16570 q selected
    | true =>
      simp only [d181956, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
  have h2 (q : Pattern) (selected : d181957 q = 0) : d182913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181957, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181958 q = 0) : d182914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181958, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181903 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
    | true =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
  have h5 (q : Pattern) (selected : d181904 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181905 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181959 q = 0) : d182915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181959, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182036 q = 0) : d182975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182036, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182036, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182037 q = 0) : d182976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182037, d182976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182037, d182976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182038 q = 0) : d182977 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182038, d182977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182038, d182977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16585 (p : Pattern) (selected : d182044 p = 0) : d182983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182034 q = 0) : d182973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182034, d182973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16583 q selected
    | true =>
      simp only [d182034, d182973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182035 q = 0) : d182974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182035, d182974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182035, d182974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182039 q = 0) : d182978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16584 q selected
    | true =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182040 q = 0) : d182979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182041 q = 0) : d182980 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182041, d182980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182041, d182980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182042 q = 0) : d182981 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182042, d182981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182042, d182981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182043 q = 0) : d182982 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182043, d182982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182043, d182982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182044 q = 0) : d182983 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182044, d182983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182044, d182983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16586 (p : Pattern) (selected : d182046 p = 0) : d182985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181903 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16562 q selected
    | true =>
      simp only [d181903, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16557 q selected
  have h2 (q : Pattern) (selected : d181904 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181904, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181905 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181905, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182036 q = 0) : d182975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182036, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182036, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182045 q = 0) : d182984 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182045, d182984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182045, d182984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182046 q = 0) : d182985 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182046, d182985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182046, d182985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16587 (p : Pattern) (selected : d182052 p = 0) : d182991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182039 q = 0) : d182978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16584 q selected
    | true =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182040 q = 0) : d182979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182047 q = 0) : d182986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182047, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16586 q selected
    | true =>
      simp only [d182047, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182048 q = 0) : d182987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182048, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182048, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182049 q = 0) : d182988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182049, d182988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182049, d182988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182050 q = 0) : d182989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182050, d182989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182050, d182989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182051 q = 0) : d182990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182051, d182990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182051, d182990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182052 q = 0) : d182991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182052, d182991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182052, d182991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16588 (p : Pattern) (selected : d182060 p = 0) : d182911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182054 q = 0) : d182905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182054, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d182054, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182055 q = 0) : d182906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182055, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182055, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181969 q = 0) : d182872 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181969, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d181969, d182872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181970 q = 0) : d182873 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181970, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181970, d182873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182056 q = 0) : d182907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182056, d182907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182056, d182907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182057 q = 0) : d182908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182057, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d182057, d182908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182058 q = 0) : d182909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182058, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182058, d182909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181916 q = 0) : d182840 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d181916, d182840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181917 q = 0) : d182841 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d181917, d182841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182059 q = 0) : d182910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182059, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182059, d182910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182060 q = 0) : d182911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182060, d182911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182060, d182911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16589 (p : Pattern) (selected : d182067 p = 0) : d182977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182061 q = 0) : d182912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182061, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16588 q selected
    | true =>
      simp only [d182061, d182912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16573 q selected
  have h2 (q : Pattern) (selected : d182062 q = 0) : d182913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182062, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182062, d182913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182063 q = 0) : d182914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182063, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182063, d182914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181973 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16573 q selected
    | true =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16565 q selected
  have h5 (q : Pattern) (selected : d181974 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181975 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182064 q = 0) : d182915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182064, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182064, d182915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182065 q = 0) : d182975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182065, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182065, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182066 q = 0) : d182976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182066, d182976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182066, d182976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182067 q = 0) : d182977 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182067, d182977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182067, d182977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16590 (p : Pattern) (selected : d182071 p = 0) : d182985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181973 q = 0) : d182876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16573 q selected
    | true =>
      simp only [d181973, d182876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16565 q selected
  have h2 (q : Pattern) (selected : d181974 q = 0) : d182877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, d182877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181975 q = 0) : d182878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, d182878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182065 q = 0) : d182975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182065, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182065, d182975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182070 q = 0) : d182984 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182070, d182984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182070, d182984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182071 q = 0) : d182985 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182071, d182985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182071, d182985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16591 (p : Pattern) (selected : d182077 p = 0) : d182991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182068 q = 0) : d182978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182068, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16589 q selected
    | true =>
      simp only [d182068, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182069 q = 0) : d182979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182069, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182069, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182072 q = 0) : d182986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182072, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16590 q selected
    | true =>
      simp only [d182072, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182073 q = 0) : d182987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182073, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182073, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182074 q = 0) : d182988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182074, d182988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182074, d182988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182075 q = 0) : d182989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182075, d182989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182075, d182989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182076 q = 0) : d182990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182076, d182990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182076, d182990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182077 q = 0) : d182991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182077, d182991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182077, d182991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16592 (p : Pattern) (selected : d182081 p = 0) : d182996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182072 q = 0) : d182986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182072, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16590 q selected
    | true =>
      simp only [d182072, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182073 q = 0) : d182987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182073, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182073, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182078 q = 0) : d182993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182078, d182993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182078, d182993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182079 q = 0) : d182994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182079, d182994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182079, d182994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182080 q = 0) : d182995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182080, d182995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182080, d182995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182081 q = 0) : d182996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182081, d182996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182081, d182996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16593 (p : Pattern) (selected : d182087 p = 0) : d183002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182039 q = 0) : d182978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16584 q selected
    | true =>
      simp only [d182039, d182978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182040 q = 0) : d182979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182040, d182979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182084 q = 0) : d182999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182084, d182999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182084, d182999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182085 q = 0) : d183000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182085, d183000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182085, d183000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182086 q = 0) : d183001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182086, d183001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182086, d183001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182087 q = 0) : d183002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182087, d183002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182087, d183002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16594 (p : Pattern) (selected : d182093 p = 0) : d183008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182053 q = 0) : d182992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182053, d182992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16585 q selected
    | true =>
      simp only [d182053, d182992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16587 q selected
  have h2 (q : Pattern) (selected : d182082 q = 0) : d182997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182082, d182997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16591 q selected
    | true =>
      simp only [d182082, d182997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16592 q selected
  have h3 (q : Pattern) (selected : d182083 q = 0) : d182998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182083, d182998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182083, d182998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182088 q = 0) : d183003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182088, d183003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16593 q selected
    | true =>
      simp only [d182088, d183003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182089 q = 0) : d183004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182089, d183004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182089, d183004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182090 q = 0) : d183005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182090, d183005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182090, d183005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182091 q = 0) : d183006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182091, d183006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182091, d183006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182092 q = 0) : d183007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182092, d183007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182092, d183007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182093 q = 0) : d183008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182093, d183008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182093, d183008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16595 (p : Pattern) (selected : d182098 p = 0) : d182996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182047 q = 0) : d182986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182047, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16586 q selected
    | true =>
      simp only [d182047, d182986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182048 q = 0) : d182987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182048, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182048, d182987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182095 q = 0) : d182993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182095, d182993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182095, d182993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182096 q = 0) : d182994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182096, d182994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182096, d182994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182097 q = 0) : d182995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182097, d182995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182097, d182995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182098 q = 0) : d182996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182098, d182996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182098, d182996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16596 (p : Pattern) (selected : d182104 p = 0) : d183015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182099 q = 0) : d183010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182099, d183010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16595 q selected
    | true =>
      simp only [d182099, d183010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182100 q = 0) : d183011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182100, d183011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182100, d183011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182101 q = 0) : d183012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182101, d183012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182101, d183012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182102 q = 0) : d183013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182102, d183013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182102, d183013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182103 q = 0) : d183014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182103, d183014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182103, d183014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182104 q = 0) : d183015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182104, d183015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182104, d183015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16597 (p : Pattern) (selected : d182110 p = 0) : d183021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182094 q = 0) : d183009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182094, d183009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182094, d183009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16594 q selected
  have h2 (q : Pattern) (selected : d182105 q = 0) : d183016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182105, d183016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182105, d183016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16596 q selected
  have h3 (q : Pattern) (selected : d182106 q = 0) : d183017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182106, d183017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182106, d183017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182107 q = 0) : d183018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182107, d183018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182107, d183018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182108 q = 0) : d183019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182108, d183019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182108, d183019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182109 q = 0) : d183020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182109, d183020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182109, d183020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182110 q = 0) : d183021 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182110, d183021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182110, d183021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16598 (p : Pattern) (selected : d182116 p = 0) : d183027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182111 q = 0) : d183022 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182111, d183022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182111, d183022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16597 q selected
  have h2 (q : Pattern) (selected : d182112 q = 0) : d183023 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182112, d183023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182112, d183023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182113 q = 0) : d183024 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182113, d183024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182113, d183024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182114 q = 0) : d183025 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182114, d183025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182114, d183025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182115 q = 0) : d183026 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182115, d183026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182115, d183026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182116 q = 0) : d183027 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182116, d183027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182116, d183027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16599 (p : Pattern) (selected : d182126 p = 0) : d183037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182118 q = 0) : d183029 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182118, d183029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d182118, d183029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182119 q = 0) : d183030 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182119, d183030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182119, d183030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182120 q = 0) : d183031 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182120, d183031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d182120, d183031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182121 q = 0) : d183032 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182121, d183032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182121, d183032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182122 q = 0) : d183033 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182122, d183033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182122, d183033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182123 q = 0) : d183034 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182123, d183034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d182123, d183034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182124 q = 0) : d183035 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182124, d183035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182124, d183035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182020 q = 0) : d182959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182021 q = 0) : d182960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182125 q = 0) : d183036 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182125, d183036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182125, d183036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182126 q = 0) : d183037 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182126, d183037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182126, d183037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16600 (p : Pattern) (selected : d182130 p = 0) : d183041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182015 q = 0) : d182954 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182015, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d182015, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182016 q = 0) : d182955 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182016, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182016, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182017 q = 0) : d182956 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182017, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d182017, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182018 q = 0) : d182957 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182018, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182018, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182019 q = 0) : d182958 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182019, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182019, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182020 q = 0) : d182959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182021 q = 0) : d182960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182127 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182128 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182129 q = 0) : d183040 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182129, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182129, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182130 q = 0) : d183041 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182130, d183041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182130, d183041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16601 (p : Pattern) (selected : d182135 p = 0) : d183046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182020 q = 0) : d182959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d182020, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182021 q = 0) : d182960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182021, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182127 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182128 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182129 q = 0) : d183040 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182129, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182129, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182134 q = 0) : d183045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182135 q = 0) : d183046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182135, d183046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182135, d183046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16602 (p : Pattern) (selected : d182141 p = 0) : d183052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d181949 q = 0) : d182905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181949, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d181949, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181950 q = 0) : d182906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181950, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181950, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182127 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182128 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182140 q = 0) : d183051 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182140, d183051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182140, d183051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182134 q = 0) : d183045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182141 q = 0) : d183052 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182141, d183052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182141, d183052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16603 (p : Pattern) (selected : d182145 p = 0) : d183056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182127 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d182127, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182128 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182128, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182134 q = 0) : d183045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182134, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182145 q = 0) : d183056 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182145, d183056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182145, d183056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16604 (p : Pattern) (selected : d182151 p = 0) : d183062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182131 q = 0) : d183042 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182131, d183042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16599 q selected
    | true =>
      simp only [d182131, d183042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16600 q selected
  have h2 (q : Pattern) (selected : d182132 q = 0) : d183043 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182132, d183043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182132, d183043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182133 q = 0) : d183044 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182133, d183044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182133, d183044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182136 q = 0) : d183047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182136, d183047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16600 q selected
    | true =>
      simp only [d182136, d183047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16601 q selected
  have h5 (q : Pattern) (selected : d182137 q = 0) : d183048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182137, d183048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182137, d183048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182138 q = 0) : d183049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182138, d183049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182138, d183049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182139 q = 0) : d183050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182139, d183050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182139, d183050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182142 q = 0) : d183053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182142, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16600 q selected
    | true =>
      simp only [d182142, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16602 q selected
  have h9 (q : Pattern) (selected : d182143 q = 0) : d183054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182143, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182143, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182144 q = 0) : d183055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182144, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182144, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182146 q = 0) : d183057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16602 q selected
    | true =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16603 q selected
  have h12 (q : Pattern) (selected : d182147 q = 0) : d183058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182148 q = 0) : d183059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182149 q = 0) : d183060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182149, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182149, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182150 q = 0) : d183061 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182150, d183061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182150, d183061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182151 q = 0) : d183062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182151, d183062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182151, d183062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16605 (p : Pattern) (selected : d182156 p = 0) : d183067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182142 q = 0) : d183053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182142, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16600 q selected
    | true =>
      simp only [d182142, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16602 q selected
  have h2 (q : Pattern) (selected : d182143 q = 0) : d183054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182143, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182143, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182144 q = 0) : d183055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182144, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182144, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182146 q = 0) : d183057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16602 q selected
    | true =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16603 q selected
  have h5 (q : Pattern) (selected : d182147 q = 0) : d183058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182148 q = 0) : d183059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182149 q = 0) : d183060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182149, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182149, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182154 q = 0) : d183065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182154, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182154, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182155 q = 0) : d183066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182155, d183066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182155, d183066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182156 q = 0) : d183067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182156, d183067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182156, d183067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16606 (p : Pattern) (selected : d182162 p = 0) : d183073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182152 q = 0) : d183063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182152, d183063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16604 q selected
    | true =>
      simp only [d182152, d183063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182153 q = 0) : d183064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182153, d183064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182153, d183064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182157 q = 0) : d183068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16605 q selected
    | true =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182158 q = 0) : d183069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182159 q = 0) : d183070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182159, d183070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182159, d183070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182160 q = 0) : d183071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182160, d183071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182160, d183071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182161 q = 0) : d183072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182161, d183072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182161, d183072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182162 q = 0) : d183073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182162, d183073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182162, d183073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16607 (p : Pattern) (selected : d182164 p = 0) : d183075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182146 q = 0) : d183057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16602 q selected
    | true =>
      simp only [d182146, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16603 q selected
  have h2 (q : Pattern) (selected : d182147 q = 0) : d183058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182147, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182148 q = 0) : d183059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182148, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182154 q = 0) : d183065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182154, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182154, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182163 q = 0) : d183074 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182163, d183074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182163, d183074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182164 q = 0) : d183075 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182164, d183075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182164, d183075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16608 (p : Pattern) (selected : d182170 p = 0) : d183081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182157 q = 0) : d183068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16605 q selected
    | true =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182158 q = 0) : d183069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182165 q = 0) : d183076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182165, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16607 q selected
    | true =>
      simp only [d182165, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182166 q = 0) : d183077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182166, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182166, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182167 q = 0) : d183078 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182167, d183078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182167, d183078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182168 q = 0) : d183079 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182168, d183079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182168, d183079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182169 q = 0) : d183080 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182169, d183080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182169, d183080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182170 q = 0) : d183081 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182170, d183081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182170, d183081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16609 (p : Pattern) (selected : d182182 p = 0) : d183041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182172 q = 0) : d182954 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182172, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d182172, d182954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182173 q = 0) : d182955 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182173, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182173, d182955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182174 q = 0) : d182956 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182174, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d182174, d182956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182175 q = 0) : d182957 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182175, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182175, d182957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182176 q = 0) : d182958 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182176, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182176, d182958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182177 q = 0) : d182959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182177, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d182177, d182959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182178 q = 0) : d182960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182178, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182178, d182960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182179 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182180 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182181 q = 0) : d183040 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182181, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182181, d183040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182182 q = 0) : d183041 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182182, d183041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182182, d183041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16610 (p : Pattern) (selected : d182185 p = 0) : d183052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182054 q = 0) : d182905 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182054, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d182054, d182905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182055 q = 0) : d182906 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182055, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182055, d182906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182179 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182180 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182183 q = 0) : d183051 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182183, d183051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182183, d183051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182184 q = 0) : d183045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182184, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182184, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182185 q = 0) : d183052 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182185, d183052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182185, d183052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16611 (p : Pattern) (selected : d182189 p = 0) : d183056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182179 q = 0) : d183038 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d182179, d183038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182180 q = 0) : d183039 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182180, d183039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182184 q = 0) : d183045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182184, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182184, d183045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182189 q = 0) : d183056 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182189, d183056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182189, d183056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16612 (p : Pattern) (selected : d182196 p = 0) : d183067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182186 q = 0) : d183053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182186, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16609 q selected
    | true =>
      simp only [d182186, d183053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16610 q selected
  have h2 (q : Pattern) (selected : d182187 q = 0) : d183054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182187, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182187, d183054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182188 q = 0) : d183055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182188, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182188, d183055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182190 q = 0) : d183057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182190, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16610 q selected
    | true =>
      simp only [d182190, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16611 q selected
  have h5 (q : Pattern) (selected : d182191 q = 0) : d183058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182191, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182191, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182192 q = 0) : d183059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182192, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182192, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182193 q = 0) : d183060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182193, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182193, d183060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182194 q = 0) : d183065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182194, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182194, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182195 q = 0) : d183066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182195, d183066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182195, d183066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182196 q = 0) : d183067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182196, d183067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182196, d183067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16613 (p : Pattern) (selected : d182200 p = 0) : d183075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182190 q = 0) : d183057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182190, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16610 q selected
    | true =>
      simp only [d182190, d183057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16611 q selected
  have h2 (q : Pattern) (selected : d182191 q = 0) : d183058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182191, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182191, d183058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182192 q = 0) : d183059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182192, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182192, d183059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182194 q = 0) : d183065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182194, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182194, d183065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182199 q = 0) : d183074 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182199, d183074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182199, d183074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182200 q = 0) : d183075 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182200, d183075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182200, d183075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16614 (p : Pattern) (selected : d182206 p = 0) : d183081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182197 q = 0) : d183068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182197, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16612 q selected
    | true =>
      simp only [d182197, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182198 q = 0) : d183069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182198, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182198, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182201 q = 0) : d183076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182201, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16613 q selected
    | true =>
      simp only [d182201, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182202 q = 0) : d183077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182202, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182202, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182203 q = 0) : d183078 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182203, d183078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182203, d183078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182204 q = 0) : d183079 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182204, d183079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182204, d183079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182205 q = 0) : d183080 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182205, d183080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182205, d183080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182206 q = 0) : d183081 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182206, d183081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182206, d183081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16615 (p : Pattern) (selected : d182210 p = 0) : d183086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182201 q = 0) : d183076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182201, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16613 q selected
    | true =>
      simp only [d182201, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182202 q = 0) : d183077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182202, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182202, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182207 q = 0) : d183083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182207, d183083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182207, d183083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182208 q = 0) : d183084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182208, d183084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182208, d183084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182209 q = 0) : d183085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182209, d183085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182209, d183085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182210 q = 0) : d183086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182210, d183086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182210, d183086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16616 (p : Pattern) (selected : d182216 p = 0) : d183092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182157 q = 0) : d183068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16605 q selected
    | true =>
      simp only [d182157, d183068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182158 q = 0) : d183069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182158, d183069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182213 q = 0) : d183089 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182213, d183089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182213, d183089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182214 q = 0) : d183090 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182214, d183090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182214, d183090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182215 q = 0) : d183091 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182215, d183091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182215, d183091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182216 q = 0) : d183092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182216, d183092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182216, d183092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16617 (p : Pattern) (selected : d182222 p = 0) : d183098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182171 q = 0) : d183082 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182171, d183082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16606 q selected
    | true =>
      simp only [d182171, d183082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16608 q selected
  have h2 (q : Pattern) (selected : d182211 q = 0) : d183087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182211, d183087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16614 q selected
    | true =>
      simp only [d182211, d183087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16615 q selected
  have h3 (q : Pattern) (selected : d182212 q = 0) : d183088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182212, d183088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182212, d183088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182217 q = 0) : d183093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182217, d183093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16616 q selected
    | true =>
      simp only [d182217, d183093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182218 q = 0) : d183094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182218, d183094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182218, d183094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182219 q = 0) : d183095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182219, d183095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182219, d183095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182220 q = 0) : d183096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182220, d183096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182220, d183096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182221 q = 0) : d183097 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182221, d183097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182221, d183097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182222 q = 0) : d183098 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182222, d183098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182222, d183098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16618 (p : Pattern) (selected : d182227 p = 0) : d183086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182165 q = 0) : d183076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182165, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16607 q selected
    | true =>
      simp only [d182165, d183076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182166 q = 0) : d183077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182166, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182166, d183077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182224 q = 0) : d183083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182224, d183083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182224, d183083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182225 q = 0) : d183084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182225, d183084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182225, d183084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182226 q = 0) : d183085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182226, d183085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182226, d183085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182227 q = 0) : d183086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182227, d183086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182227, d183086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16619 (p : Pattern) (selected : d182233 p = 0) : d183105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182228 q = 0) : d183100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182228, d183100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16618 q selected
    | true =>
      simp only [d182228, d183100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182229 q = 0) : d183101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182229, d183101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182229, d183101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182230 q = 0) : d183102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182230, d183102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182230, d183102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182231 q = 0) : d183103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182231, d183103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182231, d183103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182232 q = 0) : d183104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182232, d183104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182232, d183104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182233 q = 0) : d183105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182233, d183105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182233, d183105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16620 (p : Pattern) (selected : d182239 p = 0) : d183111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182223 q = 0) : d183099 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182223, d183099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182223, d183099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16617 q selected
  have h2 (q : Pattern) (selected : d182234 q = 0) : d183106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182234, d183106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182234, d183106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16619 q selected
  have h3 (q : Pattern) (selected : d182235 q = 0) : d183107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182235, d183107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182235, d183107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182236 q = 0) : d183108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182236, d183108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182236, d183108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182237 q = 0) : d183109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182237, d183109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182237, d183109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182238 q = 0) : d183110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182238, d183110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182238, d183110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182239 q = 0) : d183111 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182239, d183111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182239, d183111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16621 (p : Pattern) (selected : d182245 p = 0) : d183117 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182240 q = 0) : d183112 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182240, d183112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182240, d183112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16620 q selected
  have h2 (q : Pattern) (selected : d182241 q = 0) : d183113 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182241, d183113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182241, d183113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182242 q = 0) : d183114 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182242, d183114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182242, d183114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182243 q = 0) : d183115 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182243, d183115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182243, d183115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182244 q = 0) : d183116 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182244, d183116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182244, d183116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182245 q = 0) : d183117 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182245, d183117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182245, d183117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16622 (p : Pattern) (selected : d182258 p = 0) : d183130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182248 q = 0) : d183120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182248, d183120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d182248, d183120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182249 q = 0) : d183121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182249, d183121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182249, d183121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182250 q = 0) : d183122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182250, d183122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d182250, d183122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182251 q = 0) : d183123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182251, d183123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182251, d183123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182252 q = 0) : d183124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182252, d183124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182252, d183124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182253 q = 0) : d183125 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182253, d183125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d182253, d183125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182254 q = 0) : d183126 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182254, d183126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182254, d183126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182255 q = 0) : d183127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182255, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d182255, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182256 q = 0) : d183128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182256, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182256, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182257 q = 0) : d183129 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182257, d183129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182257, d183129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182258 q = 0) : d183130 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182258, d183130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182258, d183130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16623 (p : Pattern) (selected : d182267 p = 0) : d183139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182259 q = 0) : d183131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182259, d183131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d182259, d183131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182260 q = 0) : d183132 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182260, d183132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182260, d183132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182261 q = 0) : d183133 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182261, d183133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d182261, d183133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182262 q = 0) : d183134 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182262, d183134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182262, d183134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182263 q = 0) : d183135 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182263, d183135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182263, d183135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182255 q = 0) : d183127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182255, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d182255, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182256 q = 0) : d183128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182256, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182256, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182264 q = 0) : d183136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182265 q = 0) : d183137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182266 q = 0) : d183138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182266, d183138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182266, d183138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182267 q = 0) : d183139 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182267, d183139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182267, d183139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16624 (p : Pattern) (selected : d182275 p = 0) : d183147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182271 q = 0) : d183143 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182271, d183143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d182271, d183143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182272 q = 0) : d183144 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182272, d183144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182272, d183144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182264 q = 0) : d183136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182265 q = 0) : d183137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182273 q = 0) : d183145 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182273, d183145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182273, d183145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182274 q = 0) : d183146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182274, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182274, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182275 q = 0) : d183147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182275, d183147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182275, d183147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16625 (p : Pattern) (selected : d182285 p = 0) : d183157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182280 q = 0) : d183152 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182280, d183152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d182280, d183152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182281 q = 0) : d183153 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182281, d183153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182281, d183153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182282 q = 0) : d183154 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182283 q = 0) : d183155 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182284 q = 0) : d183156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182284, d183156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182284, d183156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182264 q = 0) : d183136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d182264, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182265 q = 0) : d183137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182265, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182274 q = 0) : d183146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182274, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182274, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182285 q = 0) : d183157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182285, d183157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182285, d183157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16626 (p : Pattern) (selected : d182295 p = 0) : d183167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182289 q = 0) : d183161 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182289, d183161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d182289, d183161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182290 q = 0) : d183162 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182290, d183162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182290, d183162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182291 q = 0) : d183163 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182291, d183163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182291, d183163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182292 q = 0) : d183164 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182292, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d182292, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182293 q = 0) : d183165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182293, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182293, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182294 q = 0) : d183166 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182294, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182294, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182295 q = 0) : d183167 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182295, d183167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182295, d183167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16627 (p : Pattern) (selected : d182301 p = 0) : d183173 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182268 q = 0) : d183140 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182268, d183140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16622 q selected
    | true =>
      simp only [d182268, d183140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16623 q selected
  have h2 (q : Pattern) (selected : d182269 q = 0) : d183141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182269, d183141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182269, d183141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182270 q = 0) : d183142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182270, d183142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182270, d183142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182276 q = 0) : d183148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182276, d183148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16623 q selected
    | true =>
      simp only [d182276, d183148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16624 q selected
  have h5 (q : Pattern) (selected : d182277 q = 0) : d183149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182277, d183149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182277, d183149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182278 q = 0) : d183150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182278, d183150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182278, d183150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182279 q = 0) : d183151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182279, d183151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182279, d183151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182286 q = 0) : d183158 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16623 q selected
    | true =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
  have h9 (q : Pattern) (selected : d182287 q = 0) : d183159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182288 q = 0) : d183160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182296 q = 0) : d183168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
    | true =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16626 q selected
  have h12 (q : Pattern) (selected : d182297 q = 0) : d183169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182298 q = 0) : d183170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182299 q = 0) : d183171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182300 q = 0) : d183172 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182300, d183172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182300, d183172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182301 q = 0) : d183173 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182301, d183173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182301, d183173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16628 (p : Pattern) (selected : d182306 p = 0) : d183178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182286 q = 0) : d183158 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16623 q selected
    | true =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
  have h2 (q : Pattern) (selected : d182287 q = 0) : d183159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182288 q = 0) : d183160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182296 q = 0) : d183168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
    | true =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16626 q selected
  have h5 (q : Pattern) (selected : d182297 q = 0) : d183169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182298 q = 0) : d183170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182299 q = 0) : d183171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182304 q = 0) : d183176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182304, d183176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182304, d183176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182305 q = 0) : d183177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182305, d183177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182305, d183177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182306 q = 0) : d183178 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182306, d183178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182306, d183178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16629 (p : Pattern) (selected : d182312 p = 0) : d183184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182302 q = 0) : d183174 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182302, d183174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16627 q selected
    | true =>
      simp only [d182302, d183174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182303 q = 0) : d183175 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182303, d183175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182303, d183175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182307 q = 0) : d183179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182307, d183179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16628 q selected
    | true =>
      simp only [d182307, d183179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182308 q = 0) : d183180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182308, d183180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182308, d183180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182309 q = 0) : d183181 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182309, d183181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182309, d183181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182310 q = 0) : d183182 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182310, d183182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182310, d183182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182311 q = 0) : d183183 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182311, d183183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182311, d183183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182312 q = 0) : d183184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182312, d183184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182312, d183184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16630 (p : Pattern) (selected : d182314 p = 0) : d183186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182282 q = 0) : d183154 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182283 q = 0) : d183155 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182313 q = 0) : d183185 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182313, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182313, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182292 q = 0) : d183164 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182292, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d182292, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182293 q = 0) : d183165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182293, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182293, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182294 q = 0) : d183166 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182294, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182294, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182314 q = 0) : d183186 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182314, d183186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182314, d183186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16631 (p : Pattern) (selected : d182320 p = 0) : d183192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182315 q = 0) : d183187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182315, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
    | true =>
      simp only [d182315, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16630 q selected
  have h2 (q : Pattern) (selected : d182316 q = 0) : d183188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182316, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182316, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182317 q = 0) : d183189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182317, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182317, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182318 q = 0) : d183190 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182318, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182318, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182319 q = 0) : d183191 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182319, d183191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182319, d183191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182320 q = 0) : d183192 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182320, d183192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182320, d183192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16632 (p : Pattern) (selected : d182326 p = 0) : d183198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182307 q = 0) : d183179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182307, d183179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16628 q selected
    | true =>
      simp only [d182307, d183179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182308 q = 0) : d183180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182308, d183180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182308, d183180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182321 q = 0) : d183193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182321, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16631 q selected
    | true =>
      simp only [d182321, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182322 q = 0) : d183194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182322, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182322, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182323 q = 0) : d183195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182323, d183195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182323, d183195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182324 q = 0) : d183196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182324, d183196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182324, d183196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182325 q = 0) : d183197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182325, d183197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182325, d183197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182326 q = 0) : d183198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182326, d183198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182326, d183198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16633 (p : Pattern) (selected : d182338 p = 0) : d183139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182328 q = 0) : d183131 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182328, d183131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d182328, d183131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182329 q = 0) : d183132 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182329, d183132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182329, d183132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182330 q = 0) : d183133 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182330, d183133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d182330, d183133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182331 q = 0) : d183134 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182331, d183134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182331, d183134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182332 q = 0) : d183135 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182332, d183135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182332, d183135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182333 q = 0) : d183127 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182333, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d182333, d183127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182334 q = 0) : d183128 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182334, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182334, d183128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182335 q = 0) : d183136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182335, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d182335, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182336 q = 0) : d183137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182336, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182336, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182337 q = 0) : d183138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182337, d183138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182337, d183138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182338 q = 0) : d183139 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182338, d183139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182338, d183139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16634 (p : Pattern) (selected : d182345 p = 0) : d183157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182339 q = 0) : d183152 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182339, d183152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d182339, d183152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182340 q = 0) : d183153 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182340, d183153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182340, d183153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182341 q = 0) : d183154 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182341, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d182341, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182342 q = 0) : d183155 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182342, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182342, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182343 q = 0) : d183156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182343, d183156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182343, d183156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182335 q = 0) : d183136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182335, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d182335, d183136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182336 q = 0) : d183137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182336, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182336, d183137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182344 q = 0) : d183146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182344, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182344, d183146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182345 q = 0) : d183157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182345, d183157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182345, d183157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16635 (p : Pattern) (selected : d182355 p = 0) : d183167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182349 q = 0) : d183161 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182349, d183161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d182349, d183161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182350 q = 0) : d183162 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182350, d183162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182350, d183162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182351 q = 0) : d183163 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182351, d183163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182351, d183163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182352 q = 0) : d183164 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182352, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d182352, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182353 q = 0) : d183165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182353, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182353, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182354 q = 0) : d183166 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182354, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182354, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182355 q = 0) : d183167 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182355, d183167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182355, d183167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16636 (p : Pattern) (selected : d182361 p = 0) : d183186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182341 q = 0) : d183154 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182341, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d182341, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182342 q = 0) : d183155 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182342, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182342, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182360 q = 0) : d183185 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182360, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182360, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182352 q = 0) : d183164 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182352, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d182352, d183164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182353 q = 0) : d183165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182353, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182353, d183165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182354 q = 0) : d183166 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182354, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182354, d183166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182361 q = 0) : d183186 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182361, d183186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182361, d183186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16637 (p : Pattern) (selected : d182367 p = 0) : d183201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182346 q = 0) : d183158 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182346, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16633 q selected
    | true =>
      simp only [d182346, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16634 q selected
  have h2 (q : Pattern) (selected : d182347 q = 0) : d183159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182347, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182347, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182348 q = 0) : d183160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182348, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182348, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182356 q = 0) : d183168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182356, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16634 q selected
    | true =>
      simp only [d182356, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16635 q selected
  have h5 (q : Pattern) (selected : d182357 q = 0) : d183169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182357, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182357, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182358 q = 0) : d183170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182358, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182358, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182359 q = 0) : d183171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182359, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182359, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182362 q = 0) : d183187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182362, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16634 q selected
    | true =>
      simp only [d182362, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16636 q selected
  have h9 (q : Pattern) (selected : d182363 q = 0) : d183188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182363, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182363, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182364 q = 0) : d183189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182364, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182364, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182365 q = 0) : d183190 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182365, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182365, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182366 q = 0) : d183200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182366, d183200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182366, d183200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182367 q = 0) : d183201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182367, d183201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182367, d183201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16638 (p : Pattern) (selected : d182371 p = 0) : d183192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182362 q = 0) : d183187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182362, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16634 q selected
    | true =>
      simp only [d182362, d183187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16636 q selected
  have h2 (q : Pattern) (selected : d182363 q = 0) : d183188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182363, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182363, d183188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182364 q = 0) : d183189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182364, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182364, d183189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182365 q = 0) : d183190 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182365, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182365, d183190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182370 q = 0) : d183191 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182370, d183191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182370, d183191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182371 q = 0) : d183192 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182371, d183192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182371, d183192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16639 (p : Pattern) (selected : d182377 p = 0) : d183207 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182368 q = 0) : d183202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182368, d183202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16637 q selected
    | true =>
      simp only [d182368, d183202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182369 q = 0) : d183203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182369, d183203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182369, d183203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182372 q = 0) : d183193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182372, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16638 q selected
    | true =>
      simp only [d182372, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182373 q = 0) : d183194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182373, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182373, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182374 q = 0) : d183204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182374, d183204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182374, d183204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182375 q = 0) : d183205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182375, d183205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182375, d183205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182376 q = 0) : d183206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182376, d183206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182376, d183206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182377 q = 0) : d183207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182377, d183207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182377, d183207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16640 (p : Pattern) (selected : d182381 p = 0) : d183211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182372 q = 0) : d183193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182372, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16638 q selected
    | true =>
      simp only [d182372, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182373 q = 0) : d183194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182373, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182373, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182378 q = 0) : d183208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182378, d183208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182378, d183208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182379 q = 0) : d183209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182379, d183209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182379, d183209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182380 q = 0) : d183210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182380, d183210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182380, d183210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182381 q = 0) : d183211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182381, d183211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182381, d183211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16641 (p : Pattern) (selected : d182384 p = 0) : d183214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182282 q = 0) : d183154 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d182282, d183154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182283 q = 0) : d183155 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182283, d183155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182313 q = 0) : d183185 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182313, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182313, d183185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182384 q = 0) : d183214 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182384, d183214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182384, d183214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16642 (p : Pattern) (selected : d182390 p = 0) : d183220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182286 q = 0) : d183158 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16623 q selected
    | true =>
      simp only [d182286, d183158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
  have h2 (q : Pattern) (selected : d182287 q = 0) : d183159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182287, d183159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182288 q = 0) : d183160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182288, d183160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182296 q = 0) : d183168 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
    | true =>
      simp only [d182296, d183168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16626 q selected
  have h5 (q : Pattern) (selected : d182297 q = 0) : d183169 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182297, d183169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182298 q = 0) : d183170 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182298, d183170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182299 q = 0) : d183171 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182299, d183171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182385 q = 0) : d183215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182385, d183215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16625 q selected
    | true =>
      simp only [d182385, d183215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16641 q selected
  have h9 (q : Pattern) (selected : d182386 q = 0) : d183216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182386, d183216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182386, d183216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182387 q = 0) : d183217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182387, d183217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182387, d183217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182388 q = 0) : d183218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182388, d183218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182388, d183218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182389 q = 0) : d183219 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182389, d183219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182389, d183219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182390 q = 0) : d183220 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182390, d183220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182390, d183220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16643 (p : Pattern) (selected : d182396 p = 0) : d183226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182391 q = 0) : d183221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182391, d183221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16642 q selected
    | true =>
      simp only [d182391, d183221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182392 q = 0) : d183222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182392, d183222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182392, d183222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182393 q = 0) : d183223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182393, d183223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182393, d183223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182394 q = 0) : d183224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182394, d183224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182394, d183224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182395 q = 0) : d183225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182395, d183225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182395, d183225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182396 q = 0) : d183226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182396, d183226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182396, d183226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16644 (p : Pattern) (selected : d182402 p = 0) : d183232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182327 q = 0) : d183199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182327, d183199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16629 q selected
    | true =>
      simp only [d182327, d183199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16632 q selected
  have h2 (q : Pattern) (selected : d182382 q = 0) : d183212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182382, d183212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16639 q selected
    | true =>
      simp only [d182382, d183212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16640 q selected
  have h3 (q : Pattern) (selected : d182383 q = 0) : d183213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182383, d183213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182383, d183213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182397 q = 0) : d183227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182397, d183227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16643 q selected
    | true =>
      simp only [d182397, d183227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182398 q = 0) : d183228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182398, d183228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182398, d183228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182399 q = 0) : d183229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182399, d183229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182399, d183229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182400 q = 0) : d183230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182400, d183230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182400, d183230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182401 q = 0) : d183231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182401, d183231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182401, d183231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182402 q = 0) : d183232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182402, d183232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182402, d183232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16645 (p : Pattern) (selected : d182407 p = 0) : d183211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182321 q = 0) : d183193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182321, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16631 q selected
    | true =>
      simp only [d182321, d183193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182322 q = 0) : d183194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182322, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182322, d183194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182404 q = 0) : d183208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182404, d183208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182404, d183208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182405 q = 0) : d183209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182405, d183209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182405, d183209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182406 q = 0) : d183210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182406, d183210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182406, d183210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182407 q = 0) : d183211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182407, d183211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182407, d183211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16646 (p : Pattern) (selected : d182413 p = 0) : d183239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182408 q = 0) : d183234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182408, d183234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16645 q selected
    | true =>
      simp only [d182408, d183234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182409 q = 0) : d183235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182409, d183235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182409, d183235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182410 q = 0) : d183236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182410, d183236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182410, d183236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182411 q = 0) : d183237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182411, d183237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182411, d183237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182412 q = 0) : d183238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182412, d183238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182412, d183238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182413 q = 0) : d183239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182413, d183239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182413, d183239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16647 (p : Pattern) (selected : d182419 p = 0) : d183245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182403 q = 0) : d183233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182403, d183233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182403, d183233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16644 q selected
  have h2 (q : Pattern) (selected : d182414 q = 0) : d183240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182414, d183240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182414, d183240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16646 q selected
  have h3 (q : Pattern) (selected : d182415 q = 0) : d183241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182415, d183241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182415, d183241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182416 q = 0) : d183242 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182416, d183242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182416, d183242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182417 q = 0) : d183243 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182417, d183243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182417, d183243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182418 q = 0) : d183244 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182418, d183244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182418, d183244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182419 q = 0) : d183245 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182419, d183245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182419, d183245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16648 (p : Pattern) (selected : d182425 p = 0) : d183251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182420 q = 0) : d183246 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182420, d183246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182420, d183246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16647 q selected
  have h2 (q : Pattern) (selected : d182421 q = 0) : d183247 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182421, d183247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182421, d183247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182422 q = 0) : d183248 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182422, d183248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182422, d183248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182423 q = 0) : d183249 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182423, d183249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182423, d183249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182424 q = 0) : d183250 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182424, d183250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182424, d183250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182425 q = 0) : d183251 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182425, d183251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182425, d183251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16649 (p : Pattern) (selected : d182439 p = 0) : d183265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182429 q = 0) : d183255 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182429, d183255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d182429, d183255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182430 q = 0) : d183256 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182430, d183256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182430, d183256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182431 q = 0) : d183257 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182431, d183257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d182431, d183257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182432 q = 0) : d183258 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182432, d183258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182432, d183258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182433 q = 0) : d183259 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182433, d183259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182433, d183259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182434 q = 0) : d183260 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182434, d183260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d182434, d183260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182435 q = 0) : d183261 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182435, d183261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182435, d183261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182436 q = 0) : d183262 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182436, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d182436, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182437 q = 0) : d183263 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182437, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182437, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182438 q = 0) : d183264 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182438, d183264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182438, d183264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182439 q = 0) : d183265 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182439, d183265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182439, d183265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16650 (p : Pattern) (selected : d182448 p = 0) : d183274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182440 q = 0) : d183266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182440, d183266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d182440, d183266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182441 q = 0) : d183267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182441, d183267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182441, d183267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182442 q = 0) : d183268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182442, d183268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d182442, d183268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182443 q = 0) : d183269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182443, d183269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182443, d183269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182444 q = 0) : d183270 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182444, d183270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182444, d183270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182436 q = 0) : d183262 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182436, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d182436, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182437 q = 0) : d183263 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182437, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182437, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182445 q = 0) : d183271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182446 q = 0) : d183272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182447 q = 0) : d183273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182447, d183273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182447, d183273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182448 q = 0) : d183274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182448, d183274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182448, d183274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16651 (p : Pattern) (selected : d182456 p = 0) : d183282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182452 q = 0) : d183278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182452, d183278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d182452, d183278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182453 q = 0) : d183279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182453, d183279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182453, d183279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182445 q = 0) : d183271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182446 q = 0) : d183272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182454 q = 0) : d183280 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182454, d183280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182454, d183280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182455 q = 0) : d183281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182455, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182455, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182456 q = 0) : d183282 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182456, d183282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182456, d183282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16652 (p : Pattern) (selected : d182466 p = 0) : d183292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182461 q = 0) : d183287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182461, d183287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d182461, d183287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182462 q = 0) : d183288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182462, d183288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182462, d183288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182463 q = 0) : d183289 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182463, d183289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d182463, d183289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182464 q = 0) : d183290 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182464, d183290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182464, d183290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182465 q = 0) : d183291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182465, d183291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182465, d183291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182445 q = 0) : d183271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d182445, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182446 q = 0) : d183272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182446, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182455 q = 0) : d183281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182455, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182455, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182466 q = 0) : d183292 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182466, d183292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182466, d183292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16653 (p : Pattern) (selected : d182476 p = 0) : d183302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182470 q = 0) : d183296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182470, d183296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d182470, d183296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182471 q = 0) : d183297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182471, d183297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182471, d183297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182472 q = 0) : d183298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182472, d183298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182472, d183298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182473 q = 0) : d183299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182473, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d182473, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182474 q = 0) : d183300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182474, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182474, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182475 q = 0) : d183301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182475, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182475, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182476 q = 0) : d183302 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182476, d183302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182476, d183302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16654 (p : Pattern) (selected : d182482 p = 0) : d183308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182449 q = 0) : d183275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182449, d183275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16649 q selected
    | true =>
      simp only [d182449, d183275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16650 q selected
  have h2 (q : Pattern) (selected : d182450 q = 0) : d183276 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182450, d183276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182450, d183276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182451 q = 0) : d183277 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182451, d183277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182451, d183277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182457 q = 0) : d183283 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182457, d183283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16650 q selected
    | true =>
      simp only [d182457, d183283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16651 q selected
  have h5 (q : Pattern) (selected : d182458 q = 0) : d183284 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182458, d183284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182458, d183284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182459 q = 0) : d183285 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182459, d183285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182459, d183285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182460 q = 0) : d183286 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182460, d183286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182460, d183286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182467 q = 0) : d183293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16650 q selected
    | true =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
  have h9 (q : Pattern) (selected : d182468 q = 0) : d183294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182469 q = 0) : d183295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182477 q = 0) : d183303 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
    | true =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16653 q selected
  have h12 (q : Pattern) (selected : d182478 q = 0) : d183304 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182479 q = 0) : d183305 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182480 q = 0) : d183306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182481 q = 0) : d183307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182481, d183307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182481, d183307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182482 q = 0) : d183308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182482, d183308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182482, d183308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16655 (p : Pattern) (selected : d182487 p = 0) : d183313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182467 q = 0) : d183293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16650 q selected
    | true =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
  have h2 (q : Pattern) (selected : d182468 q = 0) : d183294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182469 q = 0) : d183295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182477 q = 0) : d183303 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
    | true =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16653 q selected
  have h5 (q : Pattern) (selected : d182478 q = 0) : d183304 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182479 q = 0) : d183305 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182480 q = 0) : d183306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182485 q = 0) : d183311 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182485, d183311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182485, d183311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182486 q = 0) : d183312 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182486, d183312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182486, d183312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182487 q = 0) : d183313 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182487, d183313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182487, d183313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16656 (p : Pattern) (selected : d182493 p = 0) : d183319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182483 q = 0) : d183309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182483, d183309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16654 q selected
    | true =>
      simp only [d182483, d183309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182484 q = 0) : d183310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182484, d183310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182484, d183310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182488 q = 0) : d183314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182488, d183314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16655 q selected
    | true =>
      simp only [d182488, d183314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182489 q = 0) : d183315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182489, d183315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182489, d183315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182490 q = 0) : d183316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182490, d183316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182490, d183316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182491 q = 0) : d183317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182491, d183317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182491, d183317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182492 q = 0) : d183318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182492, d183318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182492, d183318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182493 q = 0) : d183319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182493, d183319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182493, d183319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16657 (p : Pattern) (selected : d182497 p = 0) : d183323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182494 q = 0) : d183320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182494, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d182494, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182495 q = 0) : d183321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182495, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182495, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182496 q = 0) : d183322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182496, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182496, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182473 q = 0) : d183299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182473, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d182473, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182474 q = 0) : d183300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182474, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182474, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182475 q = 0) : d183301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182475, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182475, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182497 q = 0) : d183323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182497, d183323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182497, d183323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16658 (p : Pattern) (selected : d182503 p = 0) : d183329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182498 q = 0) : d183324 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182498, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
    | true =>
      simp only [d182498, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16657 q selected
  have h2 (q : Pattern) (selected : d182499 q = 0) : d183325 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182499, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182499, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182500 q = 0) : d183326 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182500, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182500, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182501 q = 0) : d183327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182501, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182501, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182502 q = 0) : d183328 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182502, d183328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182502, d183328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182503 q = 0) : d183329 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182503, d183329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182503, d183329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16659 (p : Pattern) (selected : d182509 p = 0) : d183335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182488 q = 0) : d183314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182488, d183314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16655 q selected
    | true =>
      simp only [d182488, d183314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182489 q = 0) : d183315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182489, d183315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182489, d183315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182504 q = 0) : d183330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182504, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16658 q selected
    | true =>
      simp only [d182504, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182505 q = 0) : d183331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182505, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182505, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182506 q = 0) : d183332 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182506, d183332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182506, d183332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182507 q = 0) : d183333 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182507, d183333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182507, d183333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182508 q = 0) : d183334 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182508, d183334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182508, d183334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182509 q = 0) : d183335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182509, d183335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182509, d183335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16660 (p : Pattern) (selected : d182521 p = 0) : d183274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182511 q = 0) : d183266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182511, d183266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d182511, d183266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182512 q = 0) : d183267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182512, d183267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182512, d183267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182513 q = 0) : d183268 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182513, d183268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d182513, d183268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182514 q = 0) : d183269 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182514, d183269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182514, d183269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182515 q = 0) : d183270 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182515, d183270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182515, d183270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182516 q = 0) : d183262 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182516, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d182516, d183262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182517 q = 0) : d183263 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182517, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182517, d183263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182518 q = 0) : d183271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182518, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d182518, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182519 q = 0) : d183272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182519, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182519, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182520 q = 0) : d183273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182520, d183273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182520, d183273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182521 q = 0) : d183274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182521, d183274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182521, d183274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16661 (p : Pattern) (selected : d182528 p = 0) : d183292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182522 q = 0) : d183287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182522, d183287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d182522, d183287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182523 q = 0) : d183288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182523, d183288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182523, d183288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182524 q = 0) : d183289 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182524, d183289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d182524, d183289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182525 q = 0) : d183290 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182525, d183290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182525, d183290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182526 q = 0) : d183291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182526, d183291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182526, d183291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182518 q = 0) : d183271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182518, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d182518, d183271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182519 q = 0) : d183272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182519, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182519, d183272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182527 q = 0) : d183281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182527, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182527, d183281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182528 q = 0) : d183292 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182528, d183292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182528, d183292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16662 (p : Pattern) (selected : d182538 p = 0) : d183302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182532 q = 0) : d183296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182532, d183296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d182532, d183296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182533 q = 0) : d183297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182533, d183297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182533, d183297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182534 q = 0) : d183298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182534, d183298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182534, d183298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182535 q = 0) : d183299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182535, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d182535, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182536 q = 0) : d183300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182536, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182536, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182537 q = 0) : d183301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182537, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182537, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182538 q = 0) : d183302 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182538, d183302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182538, d183302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16663 (p : Pattern) (selected : d182546 p = 0) : d183323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182543 q = 0) : d183320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182543, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d182543, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182544 q = 0) : d183321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182544, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182544, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182545 q = 0) : d183322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182545, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182545, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182535 q = 0) : d183299 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182535, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d182535, d183299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182536 q = 0) : d183300 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182536, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182536, d183300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182537 q = 0) : d183301 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182537, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182537, d183301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182546 q = 0) : d183323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182546, d183323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182546, d183323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16664 (p : Pattern) (selected : d182552 p = 0) : d183338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182529 q = 0) : d183293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182529, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16660 q selected
    | true =>
      simp only [d182529, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16661 q selected
  have h2 (q : Pattern) (selected : d182530 q = 0) : d183294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182530, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182530, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182531 q = 0) : d183295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182531, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182531, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182539 q = 0) : d183303 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182539, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16661 q selected
    | true =>
      simp only [d182539, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16662 q selected
  have h5 (q : Pattern) (selected : d182540 q = 0) : d183304 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182540, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182540, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182541 q = 0) : d183305 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182541, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182541, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182542 q = 0) : d183306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182542, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182542, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182547 q = 0) : d183324 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182547, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16661 q selected
    | true =>
      simp only [d182547, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16663 q selected
  have h9 (q : Pattern) (selected : d182548 q = 0) : d183325 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182548, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182548, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182549 q = 0) : d183326 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182549, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182549, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182550 q = 0) : d183327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182550, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182550, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182551 q = 0) : d183337 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182551, d183337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182551, d183337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182552 q = 0) : d183338 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182552, d183338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182552, d183338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16665 (p : Pattern) (selected : d182556 p = 0) : d183329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182547 q = 0) : d183324 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182547, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16661 q selected
    | true =>
      simp only [d182547, d183324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16663 q selected
  have h2 (q : Pattern) (selected : d182548 q = 0) : d183325 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182548, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182548, d183325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182549 q = 0) : d183326 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182549, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182549, d183326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182550 q = 0) : d183327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182550, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182550, d183327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182555 q = 0) : d183328 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182555, d183328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182555, d183328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182556 q = 0) : d183329 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182556, d183329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182556, d183329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16666 (p : Pattern) (selected : d182562 p = 0) : d183344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182553 q = 0) : d183339 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182553, d183339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16664 q selected
    | true =>
      simp only [d182553, d183339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182554 q = 0) : d183340 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182554, d183340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182554, d183340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182557 q = 0) : d183330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182557, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16665 q selected
    | true =>
      simp only [d182557, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182558 q = 0) : d183331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182558, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182558, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182559 q = 0) : d183341 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182559, d183341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182559, d183341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182560 q = 0) : d183342 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182560, d183342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182560, d183342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182561 q = 0) : d183343 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182561, d183343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182561, d183343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182562 q = 0) : d183344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182562, d183344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182562, d183344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16667 (p : Pattern) (selected : d182566 p = 0) : d183348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182557 q = 0) : d183330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182557, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16665 q selected
    | true =>
      simp only [d182557, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182558 q = 0) : d183331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182558, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182558, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182563 q = 0) : d183345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182563, d183345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182563, d183345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182564 q = 0) : d183346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182564, d183346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182564, d183346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182565 q = 0) : d183347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182565, d183347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182565, d183347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182566 q = 0) : d183348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182566, d183348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182566, d183348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16668 (p : Pattern) (selected : d182569 p = 0) : d183351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182494 q = 0) : d183320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182494, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d182494, d183320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182495 q = 0) : d183321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182495, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182495, d183321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182496 q = 0) : d183322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182496, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182496, d183322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182569 q = 0) : d183351 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182569, d183351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182569, d183351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16669 (p : Pattern) (selected : d182575 p = 0) : d183357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182467 q = 0) : d183293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16650 q selected
    | true =>
      simp only [d182467, d183293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
  have h2 (q : Pattern) (selected : d182468 q = 0) : d183294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182468, d183294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182469 q = 0) : d183295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182469, d183295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182477 q = 0) : d183303 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
    | true =>
      simp only [d182477, d183303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16653 q selected
  have h5 (q : Pattern) (selected : d182478 q = 0) : d183304 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182478, d183304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182479 q = 0) : d183305 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182479, d183305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182480 q = 0) : d183306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182480, d183306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182570 q = 0) : d183352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182570, d183352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16652 q selected
    | true =>
      simp only [d182570, d183352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16668 q selected
  have h9 (q : Pattern) (selected : d182571 q = 0) : d183353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182571, d183353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182571, d183353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182572 q = 0) : d183354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182572, d183354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182572, d183354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182573 q = 0) : d183355 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182573, d183355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182573, d183355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182574 q = 0) : d183356 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182574, d183356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182574, d183356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182575 q = 0) : d183357 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182575, d183357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182575, d183357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16670 (p : Pattern) (selected : d182581 p = 0) : d183363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182576 q = 0) : d183358 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182576, d183358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16669 q selected
    | true =>
      simp only [d182576, d183358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182577 q = 0) : d183359 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182577, d183359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182577, d183359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182578 q = 0) : d183360 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182578, d183360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182578, d183360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182579 q = 0) : d183361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182579, d183361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182579, d183361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182580 q = 0) : d183362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182580, d183362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182580, d183362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182581 q = 0) : d183363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182581, d183363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182581, d183363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16671 (p : Pattern) (selected : d182587 p = 0) : d183369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182510 q = 0) : d183336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182510, d183336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16656 q selected
    | true =>
      simp only [d182510, d183336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16659 q selected
  have h2 (q : Pattern) (selected : d182567 q = 0) : d183349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182567, d183349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16666 q selected
    | true =>
      simp only [d182567, d183349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16667 q selected
  have h3 (q : Pattern) (selected : d182568 q = 0) : d183350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182568, d183350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182568, d183350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182582 q = 0) : d183364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182582, d183364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16670 q selected
    | true =>
      simp only [d182582, d183364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182583 q = 0) : d183365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182583, d183365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182583, d183365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182584 q = 0) : d183366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182584, d183366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182584, d183366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182585 q = 0) : d183367 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182585, d183367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182585, d183367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182586 q = 0) : d183368 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182586, d183368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182586, d183368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182587 q = 0) : d183369 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182587, d183369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182587, d183369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16672 (p : Pattern) (selected : d182592 p = 0) : d183348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182504 q = 0) : d183330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182504, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16658 q selected
    | true =>
      simp only [d182504, d183330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182505 q = 0) : d183331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182505, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182505, d183331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182589 q = 0) : d183345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182589, d183345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182589, d183345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182590 q = 0) : d183346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182590, d183346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182590, d183346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182591 q = 0) : d183347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182591, d183347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182591, d183347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182592 q = 0) : d183348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182592, d183348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182592, d183348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16673 (p : Pattern) (selected : d182598 p = 0) : d183376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182593 q = 0) : d183371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182593, d183371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16672 q selected
    | true =>
      simp only [d182593, d183371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182594 q = 0) : d183372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182594, d183372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182594, d183372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182595 q = 0) : d183373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182595, d183373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182595, d183373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182596 q = 0) : d183374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182596, d183374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182596, d183374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182597 q = 0) : d183375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182597, d183375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182597, d183375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182598 q = 0) : d183376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182598, d183376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182598, d183376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16674 (p : Pattern) (selected : d182604 p = 0) : d183382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182588 q = 0) : d183370 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182588, d183370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182588, d183370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16671 q selected
  have h2 (q : Pattern) (selected : d182599 q = 0) : d183377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182599, d183377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182599, d183377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16673 q selected
  have h3 (q : Pattern) (selected : d182600 q = 0) : d183378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182600, d183378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182600, d183378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182601 q = 0) : d183379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182601, d183379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182601, d183379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182602 q = 0) : d183380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182602, d183380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182602, d183380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182603 q = 0) : d183381 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182603, d183381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182603, d183381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182604 q = 0) : d183382 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182604, d183382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182604, d183382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16675 (p : Pattern) (selected : d182610 p = 0) : d183388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182605 q = 0) : d183383 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182605, d183383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182605, d183383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16674 q selected
  have h2 (q : Pattern) (selected : d182606 q = 0) : d183384 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182606, d183384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182606, d183384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182607 q = 0) : d183385 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182607, d183385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182607, d183385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182608 q = 0) : d183386 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182608, d183386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182608, d183386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182609 q = 0) : d183387 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182609, d183387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182609, d183387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182610 q = 0) : d183388 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182610, d183388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182610, d183388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16676 (p : Pattern) (selected : d182623 p = 0) : d183401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182615 q = 0) : d183393 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182615, d183393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d182615, d183393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182616 q = 0) : d183394 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182616, d183394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182616, d183394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182617 q = 0) : d183395 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182617, d183395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d182617, d183395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182618 q = 0) : d183396 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182618, d183396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182618, d183396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182619 q = 0) : d183397 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182619, d183397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182619, d183397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182620 q = 0) : d183398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182621 q = 0) : d183399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182622 q = 0) : d183400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182622, d183400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182622, d183400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182623 q = 0) : d183401 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182623, d183401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182623, d183401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16677 (p : Pattern) (selected : d182632 p = 0) : d183410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182624 q = 0) : d183402 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182624, d183402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d182624, d183402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182625 q = 0) : d183403 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182625, d183403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182625, d183403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182626 q = 0) : d183404 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182626, d183404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d182626, d183404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182627 q = 0) : d183405 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182627, d183405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182627, d183405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182628 q = 0) : d183406 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182628, d183406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182628, d183406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182620 q = 0) : d183398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182621 q = 0) : d183399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182629 q = 0) : d183407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182630 q = 0) : d183408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182631 q = 0) : d183409 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182631, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182631, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182632 q = 0) : d183410 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182632, d183410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182632, d183410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16678 (p : Pattern) (selected : d182637 p = 0) : d183415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182620 q = 0) : d183398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d182620, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182621 q = 0) : d183399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182621, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182629 q = 0) : d183407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182630 q = 0) : d183408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182631 q = 0) : d183409 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182631, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182631, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182636 q = 0) : d183414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182636, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182636, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182637 q = 0) : d183415 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182637, d183415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182637, d183415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16679 (p : Pattern) (selected : d182647 p = 0) : d183425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182642 q = 0) : d183420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182642, d183420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d182642, d183420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182643 q = 0) : d183421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182643, d183421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182643, d183421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182644 q = 0) : d183422 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182644, d183422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d182644, d183422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182645 q = 0) : d183423 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182645, d183423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182645, d183423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182646 q = 0) : d183424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182646, d183424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182646, d183424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182629 q = 0) : d183407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d182629, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182630 q = 0) : d183408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182630, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182636 q = 0) : d183414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182636, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182636, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182647 q = 0) : d183425 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182647, d183425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182647, d183425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16680 (p : Pattern) (selected : d182657 p = 0) : d183435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182651 q = 0) : d183429 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182651, d183429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d182651, d183429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182652 q = 0) : d183430 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182652, d183430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182652, d183430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182653 q = 0) : d183431 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182653, d183431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182653, d183431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182654 q = 0) : d183432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182654, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d182654, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182655 q = 0) : d183433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182655, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182655, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182656 q = 0) : d183434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182656, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182656, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182657 q = 0) : d183435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182657, d183435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182657, d183435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16681 (p : Pattern) (selected : d182663 p = 0) : d183441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182633 q = 0) : d183411 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182633, d183411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16676 q selected
    | true =>
      simp only [d182633, d183411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16677 q selected
  have h2 (q : Pattern) (selected : d182634 q = 0) : d183412 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182634, d183412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182634, d183412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182635 q = 0) : d183413 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182635, d183413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182635, d183413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182638 q = 0) : d183416 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182638, d183416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16677 q selected
    | true =>
      simp only [d182638, d183416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16678 q selected
  have h5 (q : Pattern) (selected : d182639 q = 0) : d183417 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182639, d183417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182639, d183417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182640 q = 0) : d183418 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182640, d183418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182640, d183418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182641 q = 0) : d183419 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182641, d183419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182641, d183419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182648 q = 0) : d183426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16677 q selected
    | true =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
  have h9 (q : Pattern) (selected : d182649 q = 0) : d183427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182650 q = 0) : d183428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182658 q = 0) : d183436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
    | true =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16680 q selected
  have h12 (q : Pattern) (selected : d182659 q = 0) : d183437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182660 q = 0) : d183438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182661 q = 0) : d183439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182662 q = 0) : d183440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182662, d183440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182662, d183440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182663 q = 0) : d183441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182663, d183441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182663, d183441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16682 (p : Pattern) (selected : d182668 p = 0) : d183446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182648 q = 0) : d183426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16677 q selected
    | true =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
  have h2 (q : Pattern) (selected : d182649 q = 0) : d183427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182650 q = 0) : d183428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182658 q = 0) : d183436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
    | true =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16680 q selected
  have h5 (q : Pattern) (selected : d182659 q = 0) : d183437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182660 q = 0) : d183438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182661 q = 0) : d183439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182666 q = 0) : d183444 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182666, d183444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182666, d183444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182667 q = 0) : d183445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182667, d183445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182667, d183445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182668 q = 0) : d183446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182668, d183446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182668, d183446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16683 (p : Pattern) (selected : d182674 p = 0) : d183452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182664 q = 0) : d183442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182664, d183442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16681 q selected
    | true =>
      simp only [d182664, d183442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182665 q = 0) : d183443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182665, d183443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182665, d183443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182669 q = 0) : d183447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182669, d183447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16682 q selected
    | true =>
      simp only [d182669, d183447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182670 q = 0) : d183448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182670, d183448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182670, d183448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182671 q = 0) : d183449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182671, d183449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182671, d183449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182672 q = 0) : d183450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182672, d183450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182672, d183450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182673 q = 0) : d183451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182673, d183451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182673, d183451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182674 q = 0) : d183452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182674, d183452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182674, d183452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16684 (p : Pattern) (selected : d182678 p = 0) : d183456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182675 q = 0) : d183453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182675, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d182675, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182676 q = 0) : d183454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182676, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182676, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182677 q = 0) : d183455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182677, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182677, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182654 q = 0) : d183432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182654, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d182654, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182655 q = 0) : d183433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182655, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182655, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182656 q = 0) : d183434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182656, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182656, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182678 q = 0) : d183456 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182678, d183456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182678, d183456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16685 (p : Pattern) (selected : d182684 p = 0) : d183462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182679 q = 0) : d183457 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182679, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
    | true =>
      simp only [d182679, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16684 q selected
  have h2 (q : Pattern) (selected : d182680 q = 0) : d183458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182680, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182680, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182681 q = 0) : d183459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182681, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182681, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182682 q = 0) : d183460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182682, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182682, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182683 q = 0) : d183461 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182683, d183461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182683, d183461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182684 q = 0) : d183462 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182684, d183462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182684, d183462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16686 (p : Pattern) (selected : d182690 p = 0) : d183468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182669 q = 0) : d183447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182669, d183447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16682 q selected
    | true =>
      simp only [d182669, d183447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182670 q = 0) : d183448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182670, d183448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182670, d183448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182685 q = 0) : d183463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182685, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16685 q selected
    | true =>
      simp only [d182685, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182686 q = 0) : d183464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182686, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182686, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182687 q = 0) : d183465 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182687, d183465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182687, d183465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182688 q = 0) : d183466 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182688, d183466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182688, d183466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182689 q = 0) : d183467 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182689, d183467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182689, d183467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182690 q = 0) : d183468 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182690, d183468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182690, d183468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16687 (p : Pattern) (selected : d182702 p = 0) : d183410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182692 q = 0) : d183402 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182692, d183402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d182692, d183402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182693 q = 0) : d183403 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182693, d183403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182693, d183403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182694 q = 0) : d183404 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182694, d183404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d182694, d183404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182695 q = 0) : d183405 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182695, d183405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182695, d183405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182696 q = 0) : d183406 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182696, d183406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182696, d183406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182697 q = 0) : d183398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182697, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d182697, d183398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182698 q = 0) : d183399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182698, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182698, d183399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182699 q = 0) : d183407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182699, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d182699, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182700 q = 0) : d183408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182700, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182700, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182701 q = 0) : d183409 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182701, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182701, d183409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182702 q = 0) : d183410 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182702, d183410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182702, d183410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16688 (p : Pattern) (selected : d182709 p = 0) : d183425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182703 q = 0) : d183420 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182703, d183420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d182703, d183420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182704 q = 0) : d183421 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182704, d183421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182704, d183421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182705 q = 0) : d183422 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182705, d183422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d182705, d183422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182706 q = 0) : d183423 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182706, d183423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182706, d183423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182707 q = 0) : d183424 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182707, d183424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182707, d183424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182699 q = 0) : d183407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182699, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d182699, d183407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182700 q = 0) : d183408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182700, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182700, d183408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182708 q = 0) : d183414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182708, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182708, d183414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182709 q = 0) : d183425 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182709, d183425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182709, d183425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16689 (p : Pattern) (selected : d182719 p = 0) : d183435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182713 q = 0) : d183429 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182713, d183429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d182713, d183429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182714 q = 0) : d183430 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182714, d183430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182714, d183430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182715 q = 0) : d183431 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182715, d183431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182715, d183431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182716 q = 0) : d183432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182716, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d182716, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182717 q = 0) : d183433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182717, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182717, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182718 q = 0) : d183434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182718, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182718, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182719 q = 0) : d183435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182719, d183435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182719, d183435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16690 (p : Pattern) (selected : d182727 p = 0) : d183456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182724 q = 0) : d183453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182724, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d182724, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182725 q = 0) : d183454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182725, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182725, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182726 q = 0) : d183455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182726, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182726, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182716 q = 0) : d183432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182716, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d182716, d183432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182717 q = 0) : d183433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182717, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182717, d183433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182718 q = 0) : d183434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182718, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182718, d183434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182727 q = 0) : d183456 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182727, d183456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182727, d183456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16691 (p : Pattern) (selected : d182733 p = 0) : d183471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182710 q = 0) : d183426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182710, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16687 q selected
    | true =>
      simp only [d182710, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16688 q selected
  have h2 (q : Pattern) (selected : d182711 q = 0) : d183427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182711, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182711, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182712 q = 0) : d183428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182712, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182712, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182720 q = 0) : d183436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182720, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16688 q selected
    | true =>
      simp only [d182720, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16689 q selected
  have h5 (q : Pattern) (selected : d182721 q = 0) : d183437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182721, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182721, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182722 q = 0) : d183438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182722, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182722, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182723 q = 0) : d183439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182723, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182723, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182728 q = 0) : d183457 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182728, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16688 q selected
    | true =>
      simp only [d182728, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16690 q selected
  have h9 (q : Pattern) (selected : d182729 q = 0) : d183458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182729, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182729, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182730 q = 0) : d183459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182730, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182730, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182731 q = 0) : d183460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182731, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182731, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182732 q = 0) : d183470 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182732, d183470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182732, d183470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182733 q = 0) : d183471 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182733, d183471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182733, d183471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16692 (p : Pattern) (selected : d182737 p = 0) : d183462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182728 q = 0) : d183457 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182728, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16688 q selected
    | true =>
      simp only [d182728, d183457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16690 q selected
  have h2 (q : Pattern) (selected : d182729 q = 0) : d183458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182729, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182729, d183458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182730 q = 0) : d183459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182730, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182730, d183459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182731 q = 0) : d183460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182731, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182731, d183460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182736 q = 0) : d183461 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182736, d183461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182736, d183461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182737 q = 0) : d183462 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182737, d183462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182737, d183462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16693 (p : Pattern) (selected : d182743 p = 0) : d183477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182734 q = 0) : d183472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182734, d183472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16691 q selected
    | true =>
      simp only [d182734, d183472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182735 q = 0) : d183473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182735, d183473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182735, d183473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182738 q = 0) : d183463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182738, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16692 q selected
    | true =>
      simp only [d182738, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182739 q = 0) : d183464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182739, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182739, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182740 q = 0) : d183474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182740, d183474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182740, d183474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182741 q = 0) : d183475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182741, d183475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182741, d183475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182742 q = 0) : d183476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182742, d183476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182742, d183476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182743 q = 0) : d183477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182743, d183477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182743, d183477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16694 (p : Pattern) (selected : d182747 p = 0) : d183481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182738 q = 0) : d183463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182738, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16692 q selected
    | true =>
      simp only [d182738, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182739 q = 0) : d183464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182739, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182739, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182744 q = 0) : d183478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182744, d183478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182744, d183478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182745 q = 0) : d183479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182745, d183479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182745, d183479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182746 q = 0) : d183480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182746, d183480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182746, d183480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182747 q = 0) : d183481 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182747, d183481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182747, d183481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16695 (p : Pattern) (selected : d182750 p = 0) : d183484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182675 q = 0) : d183453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182675, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d182675, d183453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182676 q = 0) : d183454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182676, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182676, d183454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182677 q = 0) : d183455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182677, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182677, d183455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182750 q = 0) : d183484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182750, d183484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182750, d183484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16696 (p : Pattern) (selected : d182756 p = 0) : d183490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182648 q = 0) : d183426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16677 q selected
    | true =>
      simp only [d182648, d183426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
  have h2 (q : Pattern) (selected : d182649 q = 0) : d183427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182649, d183427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182650 q = 0) : d183428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182650, d183428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182658 q = 0) : d183436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
    | true =>
      simp only [d182658, d183436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16680 q selected
  have h5 (q : Pattern) (selected : d182659 q = 0) : d183437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182659, d183437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182660 q = 0) : d183438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182660, d183438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182661 q = 0) : d183439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182661, d183439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182751 q = 0) : d183485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182751, d183485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16679 q selected
    | true =>
      simp only [d182751, d183485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16695 q selected
  have h9 (q : Pattern) (selected : d182752 q = 0) : d183486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182752, d183486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182752, d183486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182753 q = 0) : d183487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182753, d183487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182753, d183487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182754 q = 0) : d183488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182754, d183488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182754, d183488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182755 q = 0) : d183489 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182755, d183489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182755, d183489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182756 q = 0) : d183490 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182756, d183490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182756, d183490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16697 (p : Pattern) (selected : d182762 p = 0) : d183496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182757 q = 0) : d183491 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182757, d183491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16696 q selected
    | true =>
      simp only [d182757, d183491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182758 q = 0) : d183492 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182758, d183492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182758, d183492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182759 q = 0) : d183493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182759, d183493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182759, d183493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182760 q = 0) : d183494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182760, d183494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182760, d183494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182761 q = 0) : d183495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182761, d183495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182761, d183495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182762 q = 0) : d183496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182762, d183496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182762, d183496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16698 (p : Pattern) (selected : d182768 p = 0) : d183502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182691 q = 0) : d183469 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182691, d183469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16683 q selected
    | true =>
      simp only [d182691, d183469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16686 q selected
  have h2 (q : Pattern) (selected : d182748 q = 0) : d183482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182748, d183482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16693 q selected
    | true =>
      simp only [d182748, d183482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16694 q selected
  have h3 (q : Pattern) (selected : d182749 q = 0) : d183483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182749, d183483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182749, d183483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182763 q = 0) : d183497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182763, d183497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16697 q selected
    | true =>
      simp only [d182763, d183497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182764 q = 0) : d183498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182764, d183498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182764, d183498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182765 q = 0) : d183499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182765, d183499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182765, d183499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182766 q = 0) : d183500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182766, d183500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182766, d183500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182767 q = 0) : d183501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182767, d183501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182767, d183501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182768 q = 0) : d183502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182768, d183502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182768, d183502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16699 (p : Pattern) (selected : d182773 p = 0) : d183481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182685 q = 0) : d183463 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182685, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16685 q selected
    | true =>
      simp only [d182685, d183463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182686 q = 0) : d183464 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182686, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182686, d183464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182770 q = 0) : d183478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182770, d183478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182770, d183478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182771 q = 0) : d183479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182771, d183479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182771, d183479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182772 q = 0) : d183480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182772, d183480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182772, d183480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182773 q = 0) : d183481 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182773, d183481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182773, d183481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16700 (p : Pattern) (selected : d182779 p = 0) : d183509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182774 q = 0) : d183504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182774, d183504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16699 q selected
    | true =>
      simp only [d182774, d183504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182775 q = 0) : d183505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182775, d183505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182775, d183505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182776 q = 0) : d183506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182776, d183506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182776, d183506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182777 q = 0) : d183507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182777, d183507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182777, d183507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182778 q = 0) : d183508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182778, d183508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182778, d183508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182779 q = 0) : d183509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182779, d183509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182779, d183509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16701 (p : Pattern) (selected : d182785 p = 0) : d183515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182769 q = 0) : d183503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182769, d183503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182769, d183503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16698 q selected
  have h2 (q : Pattern) (selected : d182780 q = 0) : d183510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182780, d183510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182780, d183510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16700 q selected
  have h3 (q : Pattern) (selected : d182781 q = 0) : d183511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182781, d183511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182781, d183511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182782 q = 0) : d183512 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182782, d183512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182782, d183512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182783 q = 0) : d183513 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182783, d183513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182783, d183513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182784 q = 0) : d183514 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182784, d183514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182784, d183514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182785 q = 0) : d183515 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182785, d183515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182785, d183515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16702 (p : Pattern) (selected : d182791 p = 0) : d183521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182786 q = 0) : d183516 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182786, d183516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182786, d183516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16701 q selected
  have h2 (q : Pattern) (selected : d182787 q = 0) : d183517 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182787, d183517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182787, d183517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182788 q = 0) : d183518 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182788, d183518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182788, d183518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182789 q = 0) : d183519 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182789, d183519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182789, d183519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182790 q = 0) : d183520 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182790, d183520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182790, d183520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182791 q = 0) : d183521 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182791, d183521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182791, d183521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16703 (p : Pattern) (selected : d182797 p = 0) : d183527 p = 1 := by
  have h0 (q : Pattern) (selected : d182117 q = 0) : d183028 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182117, d183028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16580 q selected
    | true =>
      simp only [d182117, d183028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16598 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d182246 q = 0) : d183118 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182246, d183118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182246, d183118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16621 q selected
  have h3 (q : Pattern) (selected : d182247 q = 0) : d183119 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182247, d183119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182247, d183119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182426 q = 0) : d183252 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182426, d183252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182426, d183252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16648 q selected
  have h5 (q : Pattern) (selected : d182427 q = 0) : d183253 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182427, d183253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182427, d183253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182428 q = 0) : d183254 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182428, d183254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182428, d183254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182611 q = 0) : d183389 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182611, d183389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182611, d183389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16675 q selected
  have h8 (q : Pattern) (selected : d182612 q = 0) : d183390 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182612, d183390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182612, d183390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182613 q = 0) : d183391 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182613, d183391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182613, d183391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182614 q = 0) : d183392 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d182614, d183392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182614, d183392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182792 q = 0) : d183522 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d182792, d183522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182792, d183522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16702 q selected
  have h12 (q : Pattern) (selected : d182793 q = 0) : d183523 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d182793, d183523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182793, d183523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182794 q = 0) : d183524 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d182794, d183524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182794, d183524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d182795 q = 0) : d183525 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d182795, d183525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182795, d183525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d182796 q = 0) : d183526 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d182796, d183526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182796, d183526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d182797 q = 0) : d183527 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d182797, d183527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d182797, d183527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16704 (p : Pattern) (selected : d182803 p = 0) : d183533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182798 q = 0) : d183528 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d182798, d183528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16703 q selected
    | true =>
      simp only [d182798, d183528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182799 q = 0) : d183529 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d182799, d183529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182799, d183529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182800 q = 0) : d183530 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d182800, d183530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182800, d183530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182801 q = 0) : d183531 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d182801, d183531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182801, d183531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182802 q = 0) : d183532 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d182802, d183532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182802, d183532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182803 q = 0) : d183533 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d182803, d183533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182803, d183533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16705 (p : Pattern) (selected : d182809 p = 0) : d183539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182804 q = 0) : d183534 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d182804, d183534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16704 q selected
    | true =>
      simp only [d182804, d183534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182805 q = 0) : d183535 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d182805, d183535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182805, d183535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182806 q = 0) : d183536 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d182806, d183536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182806, d183536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182807 q = 0) : d183537 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d182807, d183537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182807, d183537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182808 q = 0) : d183538 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d182808, d183538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182808, d183538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182809 q = 0) : d183539 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d182809, d183539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182809, d183539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16706 (p : Pattern) (selected : d182815 p = 0) : d183545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182810 q = 0) : d183540 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d182810, d183540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16705 q selected
    | true =>
      simp only [d182810, d183540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182811 q = 0) : d183541 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d182811, d183541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182811, d183541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182812 q = 0) : d183542 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d182812, d183542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182812, d183542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182813 q = 0) : d183543 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d182813, d183543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182813, d183543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182814 q = 0) : d183544 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d182814, d183544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182814, d183544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182815 q = 0) : d183545 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d182815, d183545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182815, d183545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16707 (p : Pattern) (selected : d182821 p = 0) : d183551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182816 q = 0) : d183546 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d182816, d183546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16706 q selected
    | true =>
      simp only [d182816, d183546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182817 q = 0) : d183547 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d182817, d183547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182817, d183547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182818 q = 0) : d183548 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d182818, d183548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182818, d183548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182819 q = 0) : d183549 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d182819, d183549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182819, d183549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182820 q = 0) : d183550 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d182820, d183550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182820, d183550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182821 q = 0) : d183551 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d182821, d183551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182821, d183551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16708 (p : Pattern) (selected : d182827 p = 0) : d183557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182822 q = 0) : d183552 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d182822, d183552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16707 q selected
    | true =>
      simp only [d182822, d183552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182823 q = 0) : d183553 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d182823, d183553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182823, d183553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182824 q = 0) : d183554 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d182824, d183554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182824, d183554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182825 q = 0) : d183555 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d182825, d183555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182825, d183555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182826 q = 0) : d183556 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d182826, d183556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182826, d183556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182827 q = 0) : d183557 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d182827, d183557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182827, d183557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16709 (p : Pattern) (selected : d182833 p = 0) : d183563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182828 q = 0) : d183558 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d182828, d183558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16708 q selected
    | true =>
      simp only [d182828, d183558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182829 q = 0) : d183559 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d182829, d183559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182829, d183559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182830 q = 0) : d183560 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d182830, d183560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182830, d183560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182831 q = 0) : d183561 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d182831, d183561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182831, d183561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182832 q = 0) : d183562 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d182832, d183562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182832, d183562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182833 q = 0) : d183563 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d182833, d183563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182833, d183563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16710 (p : Pattern) (selected : d182839 p = 0) : d183569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182834 q = 0) : d183564 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d182834, d183564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16709 q selected
    | true =>
      simp only [d182834, d183564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182835 q = 0) : d183565 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d182835, d183565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182835, d183565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182836 q = 0) : d183566 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d182836, d183566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182836, d183566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182837 q = 0) : d183567 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d182837, d183567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182837, d183567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182838 q = 0) : d183568 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d182838, d183568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182838, d183568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182839 q = 0) : d183569 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d182839, d183569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182839, d183569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16711 (p : Pattern) (selected : d181919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181916 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181918 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181919 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16712 (p : Pattern) (selected : d181925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181920 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16711 q selected
    | true =>
      simp only [d181920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181921 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181922 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181923 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181924 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181925 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16713 (p : Pattern) (selected : d181931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16712 q selected
    | true =>
      simp only [d181926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181928 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16714 (p : Pattern) (selected : d181937 p = 1) : d184474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181915 q = 1) : d181915 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d181932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16713 q selected
    | true =>
      simp only [d181932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181933 q = 1) : d184470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181933, d184470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181933, d184470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181884 q = 1) : d181884 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d181934 q = 1) : d184471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181934, d184471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181934, d184471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181935 q = 1) : d184472 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181935, d184472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181935, d184472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181936 q = 1) : d184473 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181936, d184473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181936, d184473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181937 q = 1) : d184474 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181937, d184474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181937, d184474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16715 (p : Pattern) (selected : d181943 p = 1) : d184480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181938 q = 1) : d184475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181938, d184475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181938, d184475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16714 q selected
  have h2 (q : Pattern) (selected : d181939 q = 1) : d184476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d181939, d184476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181939, d184476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181940 q = 1) : d184477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d181940, d184477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181940, d184477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181941 q = 1) : d184478 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d181941, d184478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181941, d184478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181942 q = 1) : d184479 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d181942, d184479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181942, d184479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d181943 q = 1) : d184480 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d181943, d184480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181943, d184480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16716 (p : Pattern) (selected : d181972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d181969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181916 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181918 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d181918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d181918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181972 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d181972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16717 (p : Pattern) (selected : d181978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181973 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16716 q selected
    | true =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16711 q selected
  have h2 (q : Pattern) (selected : d181974 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181975 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181920 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16711 q selected
    | true =>
      simp only [d181920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d181921 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181922 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181976 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181923 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d181923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181977 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d181977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d181978 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d181978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d181978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16718 (p : Pattern) (selected : d181984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16717 q selected
    | true =>
      simp only [d181979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d181980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181926 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d181926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16712 q selected
    | true =>
      simp only [d181926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181927 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d181927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d181981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d181981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d181982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d181982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d181983 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d181983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d181983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d181984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d181984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16719 (p : Pattern) (selected : d181996 p = 1) : d184490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181968 q = 1) : d181968 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d181985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d181985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16718 q selected
    | true =>
      simp only [d181985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16713 q selected
  have h3 (q : Pattern) (selected : d181986 q = 1) : d184486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d181986, d184486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181986, d184486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181992 q = 1) : d181992 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d181993 q = 1) : d184487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d181993, d184487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181993, d184487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181994 q = 1) : d184488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d181994, d184488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181994, d184488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d181995 q = 1) : d184489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d181995, d184489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181995, d184489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d181996 q = 1) : d184490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d181996, d184490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181996, d184490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16720 (p : Pattern) (selected : d182008 p = 1) : d184496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181997 q = 1) : d184491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d181997, d184491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181997, d184491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16719 q selected
  have h2 (q : Pattern) (selected : d182003 q = 1) : d182003 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182004 q = 1) : d184492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182004, d184492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182004, d184492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182005 q = 1) : d184493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182005, d184493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182005, d184493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182006 q = 1) : d184494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182006, d184494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182006, d184494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182007 q = 1) : d184495 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182007, d184495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182007, d184495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182008 q = 1) : d184496 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182008, d184496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182008, d184496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16721 (p : Pattern) (selected : d182014 p = 1) : d184502 p = 1 := by
  have h0 (q : Pattern) (selected : d181898 q = 1) : d181898 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d181944 q = 1) : d184481 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d181944, d184481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181944, d184481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16715 q selected
  have h3 (q : Pattern) (selected : d181945 q = 1) : d184482 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d181945, d184482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181945, d184482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181946 q = 1) : d184483 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d181946, d184483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181946, d184483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d181947 q = 1) : d184484 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d181947, d184484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d181947, d184484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181948 q = 1) : d184485 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d181948, d184485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181948, d184485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182009 q = 1) : d184497 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182009, d184497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182009, d184497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16720 q selected
  have h8 (q : Pattern) (selected : d182010 q = 1) : d184498 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182010, d184498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182010, d184498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d182011 q = 1) : d184499 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182011, d184499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182011, d184499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182012 q = 1) : d184500 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182012, d184500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182012, d184500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182013 q = 1) : d184501 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182013, d184501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182013, d184501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d182014 q = 1) : d184502 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182014, d184502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182014, d184502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro16722 (p : Pattern) (selected : d182060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182054 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d182054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182055 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d181969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d181969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d181970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d181970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182056 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182057 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d182057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182058 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d181916 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d181916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d181917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d181917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182059 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182060 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16723 (p : Pattern) (selected : d182067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182061 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16722 q selected
    | true =>
      simp only [d182061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16716 q selected
  have h2 (q : Pattern) (selected : d182062 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182063 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d181973 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16716 q selected
    | true =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16711 q selected
  have h5 (q : Pattern) (selected : d181974 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d181975 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16724 (p : Pattern) (selected : d182071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d181973 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16716 q selected
    | true =>
      simp only [d181973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16711 q selected
  have h2 (q : Pattern) (selected : d181974 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d181975 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d181975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182070 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182071 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16725 (p : Pattern) (selected : d182077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16723 q selected
    | true =>
      simp only [d182068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16724 q selected
    | true =>
      simp only [d182072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182074 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182075 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182076 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182077 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16726 (p : Pattern) (selected : d182081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182072 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16724 q selected
    | true =>
      simp only [d182072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182073 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182078 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182079 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182080 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182081 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16727 (p : Pattern) (selected : d182093 p = 1) : d184507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182053 q = 1) : d182053 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16725 q selected
    | true =>
      simp only [d182082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16726 q selected
  have h3 (q : Pattern) (selected : d182083 q = 1) : d184503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182083, d184503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182083, d184503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182089 q = 1) : d182089 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d182090 q = 1) : d184504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182090, d184504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182090, d184504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182091 q = 1) : d184505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182091, d184505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182091, d184505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182092 q = 1) : d184506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182092, d184506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182092, d184506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182093 q = 1) : d184507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182093, d184507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182093, d184507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16728 (p : Pattern) (selected : d182110 p = 1) : d184513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182094 q = 1) : d184508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182094, d184508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182094, d184508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16727 q selected
  have h2 (q : Pattern) (selected : d182105 q = 1) : d182105 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182106 q = 1) : d184509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182106, d184509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182106, d184509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182107 q = 1) : d184510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182107, d184510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182107, d184510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182108 q = 1) : d184511 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182108, d184511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182108, d184511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182109 q = 1) : d184512 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182109, d184512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182109, d184512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182110 q = 1) : d184513 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182110, d184513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182110, d184513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16729 (p : Pattern) (selected : d182116 p = 1) : d184519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182111 q = 1) : d184514 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182111, d184514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182111, d184514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16728 q selected
  have h2 (q : Pattern) (selected : d182112 q = 1) : d184515 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182112, d184515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182112, d184515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182113 q = 1) : d184516 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182113, d184516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182113, d184516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182114 q = 1) : d184517 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182114, d184517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182114, d184517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182115 q = 1) : d184518 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182115, d184518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182115, d184518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182116 q = 1) : d184519 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182116, d184519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182116, d184519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16730 (p : Pattern) (selected : d182182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
    | true =>
      simp only [d182172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182174 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d182174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182175 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182176 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182177 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d182177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182178 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182182 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16731 (p : Pattern) (selected : d182185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182054 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d182054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182055 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182183 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182185 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16732 (p : Pattern) (selected : d182189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d182179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182189 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16733 (p : Pattern) (selected : d182196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182186 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16730 q selected
    | true =>
      simp only [d182186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16731 q selected
  have h2 (q : Pattern) (selected : d182187 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182188 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16731 q selected
    | true =>
      simp only [d182190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16732 q selected
  have h5 (q : Pattern) (selected : d182191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182193 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182195 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182196 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d182196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16734 (p : Pattern) (selected : d182200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16731 q selected
    | true =>
      simp only [d182190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16732 q selected
  have h2 (q : Pattern) (selected : d182191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182199 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182200 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16735 (p : Pattern) (selected : d182206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16733 q selected
    | true =>
      simp only [d182197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16734 q selected
    | true =>
      simp only [d182201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182203 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182204 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182205 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182206 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16736 (p : Pattern) (selected : d182210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16734 q selected
    | true =>
      simp only [d182201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16737 (p : Pattern) (selected : d182222 p = 1) : d184525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182171 q = 1) : d182171 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16735 q selected
    | true =>
      simp only [d182211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16736 q selected
  have h3 (q : Pattern) (selected : d182212 q = 1) : d184521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182212, d184521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182212, d184521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182218 q = 1) : d182218 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d182219 q = 1) : d184522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182219, d184522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182219, d184522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182220 q = 1) : d184523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182220, d184523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182220, d184523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182221 q = 1) : d184524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182221, d184524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182221, d184524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182222 q = 1) : d184525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182222, d184525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182222, d184525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16738 (p : Pattern) (selected : d182239 p = 1) : d184531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182223 q = 1) : d184526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182223, d184526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182223, d184526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16737 q selected
  have h2 (q : Pattern) (selected : d182234 q = 1) : d182234 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182235 q = 1) : d184527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182235, d184527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182235, d184527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182236 q = 1) : d184528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182236, d184528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182236, d184528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182237 q = 1) : d184529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182237, d184529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182237, d184529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182238 q = 1) : d184530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182238, d184530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182238, d184530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182239 q = 1) : d184531 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182239, d184531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182239, d184531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16739 (p : Pattern) (selected : d182245 p = 1) : d184537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182240 q = 1) : d184532 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d182240, d184532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182240, d184532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16738 q selected
  have h2 (q : Pattern) (selected : d182241 q = 1) : d184533 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d182241, d184533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182241, d184533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182242 q = 1) : d184534 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d182242, d184534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182242, d184534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182243 q = 1) : d184535 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d182243, d184535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182243, d184535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182244 q = 1) : d184536 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d182244, d184536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182244, d184536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182245 q = 1) : d184537 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d182245, d184537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182245, d184537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16740 (p : Pattern) (selected : d182338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182328 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
    | true =>
      simp only [d182328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182329 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182330 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d182330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182331 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182332 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d182333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d182335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d182336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d182337 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182338 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16741 (p : Pattern) (selected : d182345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d182339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182341 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d182341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182342 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182343 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182335 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d182335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182336 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182344 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d182345 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16742 (p : Pattern) (selected : d182355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182349 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
    | true =>
      simp only [d182349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182350 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182351 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d182352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182354 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182355 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16743 (p : Pattern) (selected : d182361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182341 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d182341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182342 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d182360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d182352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d182352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d182353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182354 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d182354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182361 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d182361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16744 (p : Pattern) (selected : d182367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182346 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16740 q selected
    | true =>
      simp only [d182346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16741 q selected
  have h2 (q : Pattern) (selected : d182347 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16741 q selected
    | true =>
      simp only [d182356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16742 q selected
  have h5 (q : Pattern) (selected : d182357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182359 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182362 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16741 q selected
    | true =>
      simp only [d182362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16743 q selected
  have h9 (q : Pattern) (selected : d182363 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d182364 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d182365 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d182365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d182366 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d182367 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d182367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16745 (p : Pattern) (selected : d182371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182362 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d182362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16741 q selected
    | true =>
      simp only [d182362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16743 q selected
  have h2 (q : Pattern) (selected : d182363 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d182363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182364 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d182364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182365 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d182365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d182370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d182371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16746 (p : Pattern) (selected : d182377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182368 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16744 q selected
    | true =>
      simp only [d182368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182369 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16745 q selected
    | true =>
      simp only [d182372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d182374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d182376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d182377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d182377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16747 (p : Pattern) (selected : d182381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16745 q selected
    | true =>
      simp only [d182372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d182373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d182378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d182378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d182379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d182379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d182380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d182381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16748 (p : Pattern) (selected : d182402 p = 1) : d184544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182327 q = 1) : d182327 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d182382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d182382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16746 q selected
    | true =>
      simp only [d182382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16747 q selected
  have h3 (q : Pattern) (selected : d182383 q = 1) : d184540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d182383, d184540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182383, d184540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182398 q = 1) : d182398 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d182399 q = 1) : d184541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d182399, d184541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182399, d184541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d182400 q = 1) : d184542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d182400, d184542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182400, d184542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d182401 q = 1) : d184543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d182401, d184543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182401, d184543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d182402 q = 1) : d184544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d182402, d184544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182402, d184544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16749 (p : Pattern) (selected : d182419 p = 1) : d184550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182403 q = 1) : d184545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d182403, d184545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182403, d184545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16748 q selected
  have h2 (q : Pattern) (selected : d182414 q = 1) : d182414 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d182415 q = 1) : d184546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d182415, d184546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d182415, d184546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d182416 q = 1) : d184547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d182416, d184547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d182416, d184547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d182417 q = 1) : d184548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d182417, d184548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d182417, d184548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d182418 q = 1) : d184549 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d182418, d184549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d182418, d184549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d182419 q = 1) : d184550 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d182419, d184550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d182419, d184550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
end NetHack.Soko22Hazard87
