import NetHack.Soko22Hazard87.EqIntroBlocks0158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro39750 (p : Pattern) (selected : d379179 p = 0) : d379223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379174 q = 0) : d379218 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379174, d379218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39749 q selected
    | true =>
      simp only [d379174, d379218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379175 q = 0) : d379219 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379175, d379219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379175, d379219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379176 q = 0) : d379220 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379176, d379220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379176, d379220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379177 q = 0) : d379221 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379177, d379221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379177, d379221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379178 q = 0) : d379222 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379178, d379222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379178, d379222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379179 q = 0) : d379223 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379179, d379223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379179, d379223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39751 (p : Pattern) (selected : d379138 p = 1) : d379226 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d379136 q = 1) : d379224 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379136, d379224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379136, d379224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d379137 q = 1) : d379225 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379137, d379225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379137, d379225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d379138 q = 1) : d379226 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379138, d379226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379138, d379226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39752 (p : Pattern) (selected : d379144 p = 1) : d379232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379139 q = 1) : d379227 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379139, d379227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39751 q selected
    | true =>
      simp only [d379139, d379227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379140 q = 1) : d379228 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379140, d379228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379140, d379228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379141 q = 1) : d379229 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379141, d379229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379141, d379229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379142 q = 1) : d379230 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379142, d379230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379142, d379230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379143 q = 1) : d379231 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379143, d379231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379143, d379231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379144 q = 1) : d379232 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379144, d379232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379144, d379232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39753 (p : Pattern) (selected : d379149 p = 1) : d379237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379145 q = 1) : d379233 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379145, d379233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39752 q selected
    | true =>
      simp only [d379145, d379233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379146 q = 1) : d379234 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379146, d379234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379146, d379234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379147 q = 1) : d379235 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379147, d379235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379147, d379235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379148 q = 1) : d379236 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379148, d379236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379148, d379236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379149 q = 1) : d379237 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379149, d379237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379149, d379237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39754 (p : Pattern) (selected : d379155 p = 1) : d379243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379150 q = 1) : d379238 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379150, d379238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39753 q selected
    | true =>
      simp only [d379150, d379238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379151 q = 1) : d379239 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379151, d379239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379151, d379239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379152 q = 1) : d379240 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379152, d379240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379152, d379240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379153 q = 1) : d379241 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379153, d379241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379153, d379241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379154 q = 1) : d379242 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379154, d379242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379154, d379242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379155 q = 1) : d379243 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379155, d379243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379155, d379243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39755 (p : Pattern) (selected : d379161 p = 1) : d379249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379156 q = 1) : d379244 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379156, d379244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39754 q selected
    | true =>
      simp only [d379156, d379244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379157 q = 1) : d379245 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379157, d379245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379157, d379245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379158 q = 1) : d379246 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379158, d379246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379158, d379246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379159 q = 1) : d379247 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379159, d379247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379159, d379247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379160 q = 1) : d379248 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379160, d379248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379160, d379248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379161 q = 1) : d379249 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379161, d379249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379161, d379249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39756 (p : Pattern) (selected : d379167 p = 1) : d379255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379162 q = 1) : d379250 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379162, d379250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39755 q selected
    | true =>
      simp only [d379162, d379250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379163 q = 1) : d379251 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379163, d379251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379163, d379251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379164 q = 1) : d379252 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379164, d379252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379164, d379252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379165 q = 1) : d379253 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379165, d379253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379165, d379253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379166 q = 1) : d379254 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379166, d379254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379166, d379254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379167 q = 1) : d379255 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379167, d379255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379167, d379255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39757 (p : Pattern) (selected : d379173 p = 1) : d379261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379168 q = 1) : d379256 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379168, d379256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39756 q selected
    | true =>
      simp only [d379168, d379256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379169 q = 1) : d379257 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379169, d379257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379169, d379257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379170 q = 1) : d379258 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379170, d379258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379170, d379258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379171 q = 1) : d379259 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379171, d379259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379171, d379259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379172 q = 1) : d379260 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379172, d379260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379172, d379260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379173 q = 1) : d379261 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379173, d379261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379173, d379261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39758 (p : Pattern) (selected : d379179 p = 1) : d379267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379174 q = 1) : d379262 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379174, d379262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39757 q selected
    | true =>
      simp only [d379174, d379262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379175 q = 1) : d379263 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379175, d379263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379175, d379263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379176 q = 1) : d379264 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379176, d379264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379176, d379264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379177 q = 1) : d379265 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379177, d379265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379177, d379265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379178 q = 1) : d379266 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379178, d379266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379178, d379266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379179 q = 1) : d379267 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379179, d379267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379179, d379267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39759 (p : Pattern) (selected : d47375 p = 0) : d379281 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47372 q = 0) : d379278 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47372, d379278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47372, d379278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47373 q = 0) : d379279 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47373, d379279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47373, d379279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47374 q = 0) : d379280 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47374, d379280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47374, d379280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d47375 q = 0) : d379281 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47375, d379281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47375, d379281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro39760 (p : Pattern) (selected : d47381 p = 0) : d379287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47376 q = 0) : d379282 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47376, d379282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39759 q selected
    | true =>
      simp only [d47376, d379282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47377 q = 0) : d379283 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47377, d379283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47377, d379283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47378 q = 0) : d379284 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47378, d379284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47378, d379284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47379 q = 0) : d379285 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47379, d379285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47379, d379285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47380 q = 0) : d379286 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47380, d379286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47380, d379286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47381 q = 0) : d379287 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47381, d379287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47381, d379287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39761 (p : Pattern) (selected : d47387 p = 0) : d379293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47382 q = 0) : d379288 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47382, d379288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39760 q selected
    | true =>
      simp only [d47382, d379288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47383 q = 0) : d379289 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47383, d379289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47383, d379289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47384 q = 0) : d379290 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47384, d379290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47384, d379290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47385 q = 0) : d379291 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47385, d379291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47385, d379291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47386 q = 0) : d379292 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47386, d379292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47386, d379292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47387 q = 0) : d379293 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47387, d379293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47387, d379293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39762 (p : Pattern) (selected : d47393 p = 0) : d379299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47388 q = 0) : d379294 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47388, d379294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39761 q selected
    | true =>
      simp only [d47388, d379294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47389 q = 0) : d379295 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47389, d379295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47389, d379295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47390 q = 0) : d379296 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47390, d379296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47390, d379296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47391 q = 0) : d379297 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47391, d379297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47391, d379297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47392 q = 0) : d379298 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47392, d379298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47392, d379298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47393 q = 0) : d379299 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47393, d379299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47393, d379299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39763 (p : Pattern) (selected : d47399 p = 0) : d379305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47394 q = 0) : d379300 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47394, d379300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39762 q selected
    | true =>
      simp only [d47394, d379300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47395 q = 0) : d379301 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47395, d379301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47395, d379301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47396 q = 0) : d379302 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47396, d379302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47396, d379302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47397 q = 0) : d379303 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47397, d379303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47397, d379303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47398 q = 0) : d379304 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47398, d379304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47398, d379304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47399 q = 0) : d379305 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47399, d379305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47399, d379305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39764 (p : Pattern) (selected : d47405 p = 0) : d379311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47400 q = 0) : d379306 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47400, d379306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39763 q selected
    | true =>
      simp only [d47400, d379306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47401 q = 0) : d379307 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47401, d379307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47401, d379307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47402 q = 0) : d379308 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47402, d379308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47402, d379308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47403 q = 0) : d379309 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47403, d379309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47403, d379309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47404 q = 0) : d379310 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47404, d379310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47404, d379310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47405 q = 0) : d379311 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47405, d379311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47405, d379311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39765 (p : Pattern) (selected : d47411 p = 0) : d379317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47406 q = 0) : d379312 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47406, d379312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39764 q selected
    | true =>
      simp only [d47406, d379312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47407 q = 0) : d379313 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47407, d379313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47407, d379313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47408 q = 0) : d379314 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47408, d379314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47408, d379314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47409 q = 0) : d379315 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47409, d379315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47409, d379315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47410 q = 0) : d379316 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47410, d379316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47410, d379316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47411 q = 0) : d379317 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47411, d379317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47411, d379317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39766 (p : Pattern) (selected : d47417 p = 0) : d379323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47412 q = 0) : d379318 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47412, d379318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39765 q selected
    | true =>
      simp only [d47412, d379318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47413 q = 0) : d379319 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47413, d379319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47413, d379319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47414 q = 0) : d379320 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47414, d379320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47414, d379320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47415 q = 0) : d379321 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47415, d379321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47415, d379321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47416 q = 0) : d379322 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47416, d379322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47416, d379322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47417 q = 0) : d379323 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47417, d379323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47417, d379323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39767 (p : Pattern) (selected : d47329 p = 2) : d379084 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 2) : d367652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38350 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d45903 q = 2) : d367679 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38427 q selected
  have h3 (q : Pattern) (selected : d45904 q = 2) : d367680 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 2) : d367707 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d367707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38515 q selected
  have h5 (q : Pattern) (selected : d46457 q = 2) : d367708 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d367708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 2) : d367709 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d367709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47327 q = 2) : d379082 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47327, d379082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47327, d379082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d47328 q = 2) : d379083 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47328, d379083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d47328, d379083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d47329 q = 2) : d379084 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47329, d379084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d47329, d379084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro39768 (p : Pattern) (selected : d47335 p = 2) : d379090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47330 q = 2) : d379085 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47330, d379085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39767 q selected
    | true =>
      simp only [d47330, d379085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47331 q = 2) : d379086 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47331, d379086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47331, d379086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47332 q = 2) : d379087 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47332, d379087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47332, d379087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47333 q = 2) : d379088 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47333, d379088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47333, d379088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47334 q = 2) : d379089 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47334, d379089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47334, d379089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47335 q = 2) : d379090 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47335, d379090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47335, d379090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39769 (p : Pattern) (selected : d47341 p = 2) : d379096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47336 q = 2) : d379091 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47336, d379091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39768 q selected
    | true =>
      simp only [d47336, d379091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47337 q = 2) : d379092 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47337, d379092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47337, d379092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47338 q = 2) : d379093 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47338, d379093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47338, d379093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47339 q = 2) : d379094 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47339, d379094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47339, d379094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47340 q = 2) : d379095 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47340, d379095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47340, d379095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47341 q = 2) : d379096 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47341, d379096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47341, d379096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39770 (p : Pattern) (selected : d47347 p = 2) : d379102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47342 q = 2) : d379097 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47342, d379097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39769 q selected
    | true =>
      simp only [d47342, d379097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47343 q = 2) : d379098 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47343, d379098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47343, d379098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47344 q = 2) : d379099 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47344, d379099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47344, d379099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47345 q = 2) : d379100 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47345, d379100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47345, d379100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47346 q = 2) : d379101 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47346, d379101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47346, d379101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47347 q = 2) : d379102 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47347, d379102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47347, d379102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39771 (p : Pattern) (selected : d47353 p = 2) : d379108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47348 q = 2) : d379103 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47348, d379103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39770 q selected
    | true =>
      simp only [d47348, d379103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47349 q = 2) : d379104 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47349, d379104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47349, d379104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47350 q = 2) : d379105 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47350, d379105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47350, d379105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47351 q = 2) : d379106 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47351, d379106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47351, d379106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47352 q = 2) : d379107 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47352, d379107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47352, d379107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47353 q = 2) : d379108 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47353, d379108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47353, d379108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39772 (p : Pattern) (selected : d47359 p = 2) : d379114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47354 q = 2) : d379109 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47354, d379109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39771 q selected
    | true =>
      simp only [d47354, d379109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47355 q = 2) : d379110 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47355, d379110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47355, d379110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47356 q = 2) : d379111 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47356, d379111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47356, d379111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47357 q = 2) : d379112 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47357, d379112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47357, d379112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47358 q = 2) : d379113 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47358, d379113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47358, d379113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47359 q = 2) : d379114 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47359, d379114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47359, d379114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39773 (p : Pattern) (selected : d47365 p = 2) : d379120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47360 q = 2) : d379115 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47360, d379115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39772 q selected
    | true =>
      simp only [d47360, d379115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47361 q = 2) : d379116 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47361, d379116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47361, d379116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47362 q = 2) : d379117 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47362, d379117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47362, d379117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47363 q = 2) : d379118 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47363, d379118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47363, d379118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47364 q = 2) : d379119 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47364, d379119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47364, d379119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47365 q = 2) : d379120 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47365, d379120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47365, d379120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39774 (p : Pattern) (selected : d47371 p = 2) : d379126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47366 q = 2) : d379121 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47366, d379121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39773 q selected
    | true =>
      simp only [d47366, d379121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47367 q = 2) : d379122 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47367, d379122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47367, d379122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47368 q = 2) : d379123 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47368, d379123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47368, d379123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47369 q = 2) : d379124 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47369, d379124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47369, d379124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47370 q = 2) : d379125 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47370, d379125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47370, d379125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47371 q = 2) : d379126 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47371, d379126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47371, d379126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39775 (p : Pattern) (selected : d47375 p = 1) : d379327 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47372 q = 1) : d379324 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47372, d379324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47372, d379324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47373 q = 1) : d379325 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47373, d379325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47373, d379325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47374 q = 1) : d379326 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47374, d379326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47374, d379326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d47375 q = 1) : d379327 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47375, d379327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47375, d379327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro39776 (p : Pattern) (selected : d47381 p = 1) : d379333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47376 q = 1) : d379328 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47376, d379328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39775 q selected
    | true =>
      simp only [d47376, d379328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47377 q = 1) : d379329 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47377, d379329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47377, d379329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47378 q = 1) : d379330 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47378, d379330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47378, d379330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47379 q = 1) : d379331 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47379, d379331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47379, d379331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47380 q = 1) : d379332 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47380, d379332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47380, d379332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47381 q = 1) : d379333 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47381, d379333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47381, d379333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39777 (p : Pattern) (selected : d47387 p = 1) : d379339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47382 q = 1) : d379334 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47382, d379334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39776 q selected
    | true =>
      simp only [d47382, d379334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47383 q = 1) : d379335 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47383, d379335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47383, d379335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47384 q = 1) : d379336 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47384, d379336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47384, d379336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47385 q = 1) : d379337 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47385, d379337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47385, d379337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47386 q = 1) : d379338 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47386, d379338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47386, d379338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47387 q = 1) : d379339 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47387, d379339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47387, d379339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39778 (p : Pattern) (selected : d47393 p = 1) : d379345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47388 q = 1) : d379340 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47388, d379340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39777 q selected
    | true =>
      simp only [d47388, d379340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47389 q = 1) : d379341 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47389, d379341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47389, d379341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47390 q = 1) : d379342 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47390, d379342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47390, d379342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47391 q = 1) : d379343 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47391, d379343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47391, d379343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47392 q = 1) : d379344 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47392, d379344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47392, d379344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47393 q = 1) : d379345 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47393, d379345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47393, d379345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39779 (p : Pattern) (selected : d47399 p = 1) : d379351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47394 q = 1) : d379346 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47394, d379346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39778 q selected
    | true =>
      simp only [d47394, d379346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47395 q = 1) : d379347 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47395, d379347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47395, d379347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47396 q = 1) : d379348 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47396, d379348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47396, d379348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47397 q = 1) : d379349 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47397, d379349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47397, d379349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47398 q = 1) : d379350 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47398, d379350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47398, d379350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47399 q = 1) : d379351 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47399, d379351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47399, d379351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39780 (p : Pattern) (selected : d47405 p = 1) : d379357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47400 q = 1) : d379352 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47400, d379352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39779 q selected
    | true =>
      simp only [d47400, d379352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47401 q = 1) : d379353 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47401, d379353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47401, d379353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47402 q = 1) : d379354 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47402, d379354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47402, d379354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47403 q = 1) : d379355 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47403, d379355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47403, d379355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47404 q = 1) : d379356 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47404, d379356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47404, d379356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47405 q = 1) : d379357 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47405, d379357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47405, d379357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39781 (p : Pattern) (selected : d47411 p = 1) : d379363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47406 q = 1) : d379358 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47406, d379358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39780 q selected
    | true =>
      simp only [d47406, d379358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47407 q = 1) : d379359 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47407, d379359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47407, d379359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47408 q = 1) : d379360 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47408, d379360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47408, d379360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47409 q = 1) : d379361 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47409, d379361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47409, d379361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47410 q = 1) : d379362 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47410, d379362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47410, d379362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47411 q = 1) : d379363 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47411, d379363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47411, d379363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39782 (p : Pattern) (selected : d47417 p = 1) : d379369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47412 q = 1) : d379364 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47412, d379364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39781 q selected
    | true =>
      simp only [d47412, d379364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47413 q = 1) : d379365 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47413, d379365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47413, d379365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47414 q = 1) : d379366 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47414, d379366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47414, d379366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47415 q = 1) : d379367 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47415, d379367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47415, d379367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47416 q = 1) : d379368 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47416, d379368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47416, d379368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47417 q = 1) : d379369 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47417, d379369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47417, d379369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39783 (p : Pattern) (selected : d379428 p = 0) : d379473 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d379425 q = 0) : d379470 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379425, d379470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d379425, d379470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d379426 q = 0) : d379471 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379426, d379471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379426, d379471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d379427 q = 0) : d379472 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379427, d379472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379427, d379472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d379428 q = 0) : d379473 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379428, d379473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379428, d379473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro39784 (p : Pattern) (selected : d379434 p = 0) : d379479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379429 q = 0) : d379474 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379429, d379474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39783 q selected
    | true =>
      simp only [d379429, d379474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379430 q = 0) : d379475 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379430, d379475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379430, d379475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379431 q = 0) : d379476 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379431, d379476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379431, d379476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379432 q = 0) : d379477 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379432, d379477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379432, d379477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379433 q = 0) : d379478 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379433, d379478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379433, d379478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379434 q = 0) : d379479 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379434, d379479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379434, d379479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39785 (p : Pattern) (selected : d379439 p = 0) : d379484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379435 q = 0) : d379480 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379435, d379480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39784 q selected
    | true =>
      simp only [d379435, d379480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379436 q = 0) : d379481 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379436, d379481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379436, d379481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379437 q = 0) : d379482 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379437, d379482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379437, d379482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379438 q = 0) : d379483 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379438, d379483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379438, d379483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379439 q = 0) : d379484 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379439, d379484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379439, d379484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39786 (p : Pattern) (selected : d379445 p = 0) : d379490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379440 q = 0) : d379485 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379440, d379485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39785 q selected
    | true =>
      simp only [d379440, d379485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379441 q = 0) : d379486 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379441, d379486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379441, d379486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379442 q = 0) : d379487 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379442, d379487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379442, d379487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379443 q = 0) : d379488 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379443, d379488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379443, d379488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379444 q = 0) : d379489 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379444, d379489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379444, d379489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379445 q = 0) : d379490 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379445, d379490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379445, d379490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39787 (p : Pattern) (selected : d379451 p = 0) : d379496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379446 q = 0) : d379491 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379446, d379491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39786 q selected
    | true =>
      simp only [d379446, d379491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379447 q = 0) : d379492 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379447, d379492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379447, d379492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379448 q = 0) : d379493 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379448, d379493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379448, d379493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379449 q = 0) : d379494 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379449, d379494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379449, d379494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379450 q = 0) : d379495 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379450, d379495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379450, d379495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379451 q = 0) : d379496 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379451, d379496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379451, d379496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39788 (p : Pattern) (selected : d379457 p = 0) : d379502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379452 q = 0) : d379497 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379452, d379497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39787 q selected
    | true =>
      simp only [d379452, d379497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379453 q = 0) : d379498 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379453, d379498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379453, d379498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379454 q = 0) : d379499 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379454, d379499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379454, d379499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379455 q = 0) : d379500 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379455, d379500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379455, d379500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379456 q = 0) : d379501 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379456, d379501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379456, d379501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379457 q = 0) : d379502 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379457, d379502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379457, d379502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39789 (p : Pattern) (selected : d379463 p = 0) : d379508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379458 q = 0) : d379503 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379458, d379503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39788 q selected
    | true =>
      simp only [d379458, d379503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379459 q = 0) : d379504 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379459, d379504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379459, d379504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379460 q = 0) : d379505 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379460, d379505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379460, d379505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379461 q = 0) : d379506 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379461, d379506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379461, d379506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379462 q = 0) : d379507 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379462, d379507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379462, d379507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379463 q = 0) : d379508 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379463, d379508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379463, d379508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39790 (p : Pattern) (selected : d379469 p = 0) : d379514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379464 q = 0) : d379509 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379464, d379509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39789 q selected
    | true =>
      simp only [d379464, d379509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379465 q = 0) : d379510 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379465, d379510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379465, d379510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379466 q = 0) : d379511 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379466, d379511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379466, d379511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379467 q = 0) : d379512 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379467, d379512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379467, d379512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379468 q = 0) : d379513 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379468, d379513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379468, d379513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379469 q = 0) : d379514 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379469, d379514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379469, d379514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39791 (p : Pattern) (selected : d379428 p = 1) : d379518 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d379425 q = 1) : d379515 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379425, d379515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d379425, d379515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d379426 q = 1) : d379516 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379426, d379516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379426, d379516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d379427 q = 1) : d379517 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379427, d379517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379427, d379517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d379428 q = 1) : d379518 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379428, d379518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379428, d379518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro39792 (p : Pattern) (selected : d379434 p = 1) : d379524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379429 q = 1) : d379519 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379429, d379519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39791 q selected
    | true =>
      simp only [d379429, d379519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379430 q = 1) : d379520 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379430, d379520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379430, d379520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379431 q = 1) : d379521 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379431, d379521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379431, d379521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379432 q = 1) : d379522 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379432, d379522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379432, d379522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379433 q = 1) : d379523 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379433, d379523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379433, d379523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379434 q = 1) : d379524 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379434, d379524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379434, d379524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39793 (p : Pattern) (selected : d379439 p = 1) : d379529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379435 q = 1) : d379525 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379435, d379525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39792 q selected
    | true =>
      simp only [d379435, d379525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379436 q = 1) : d379526 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379436, d379526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379436, d379526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379437 q = 1) : d379527 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379437, d379527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379437, d379527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379438 q = 1) : d379528 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379438, d379528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379438, d379528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379439 q = 1) : d379529 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379439, d379529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379439, d379529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39794 (p : Pattern) (selected : d379445 p = 1) : d379535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379440 q = 1) : d379530 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379440, d379530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39793 q selected
    | true =>
      simp only [d379440, d379530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379441 q = 1) : d379531 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379441, d379531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379441, d379531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379442 q = 1) : d379532 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379442, d379532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379442, d379532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379443 q = 1) : d379533 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379443, d379533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379443, d379533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379444 q = 1) : d379534 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379444, d379534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379444, d379534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379445 q = 1) : d379535 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379445, d379535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379445, d379535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39795 (p : Pattern) (selected : d379451 p = 1) : d379541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379446 q = 1) : d379536 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379446, d379536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39794 q selected
    | true =>
      simp only [d379446, d379536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379447 q = 1) : d379537 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379447, d379537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379447, d379537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379448 q = 1) : d379538 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379448, d379538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379448, d379538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379449 q = 1) : d379539 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379449, d379539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379449, d379539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379450 q = 1) : d379540 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379450, d379540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379450, d379540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379451 q = 1) : d379541 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379451, d379541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379451, d379541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39796 (p : Pattern) (selected : d379457 p = 1) : d379547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379452 q = 1) : d379542 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379452, d379542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39795 q selected
    | true =>
      simp only [d379452, d379542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379453 q = 1) : d379543 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379453, d379543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379453, d379543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379454 q = 1) : d379544 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379454, d379544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379454, d379544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379455 q = 1) : d379545 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379455, d379545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379455, d379545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379456 q = 1) : d379546 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379456, d379546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379456, d379546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379457 q = 1) : d379547 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379457, d379547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379457, d379547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39797 (p : Pattern) (selected : d379463 p = 1) : d379553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379458 q = 1) : d379548 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379458, d379548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39796 q selected
    | true =>
      simp only [d379458, d379548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379459 q = 1) : d379549 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379459, d379549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379459, d379549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379460 q = 1) : d379550 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379460, d379550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379460, d379550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379461 q = 1) : d379551 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379461, d379551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379461, d379551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379462 q = 1) : d379552 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379462, d379552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379462, d379552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379463 q = 1) : d379553 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379463, d379553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379463, d379553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39798 (p : Pattern) (selected : d379469 p = 1) : d379559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379464 q = 1) : d379554 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379464, d379554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39797 q selected
    | true =>
      simp only [d379464, d379554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379465 q = 1) : d379555 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379465, d379555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379465, d379555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379466 q = 1) : d379556 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379466, d379556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379466, d379556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379467 q = 1) : d379557 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379467, d379557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379467, d379557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379468 q = 1) : d379558 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379468, d379558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379468, d379558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379469 q = 1) : d379559 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379469, d379559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379469, d379559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39799 (p : Pattern) (selected : d47422 p = 0) : d379588 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d47418 q = 0) : d379584 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47418, d379584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47418, d379584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47419 q = 0) : d379585 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47419, d379585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47419, d379585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d47420 q = 0) : d379586 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47420, d379586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47420, d379586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47421 q = 0) : d379587 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47421, d379587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47421, d379587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47422 q = 0) : d379588 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47422, d379588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47422, d379588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39800 (p : Pattern) (selected : d47428 p = 0) : d379594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47423 q = 0) : d379589 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47423, d379589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39799 q selected
    | true =>
      simp only [d47423, d379589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47424 q = 0) : d379590 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47424, d379590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47424, d379590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47425 q = 0) : d379591 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47425, d379591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47425, d379591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47426 q = 0) : d379592 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47426, d379592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47426, d379592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47427 q = 0) : d379593 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47427, d379593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47427, d379593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47428 q = 0) : d379594 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47428, d379594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47428, d379594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39801 (p : Pattern) (selected : d47434 p = 0) : d379600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47429 q = 0) : d379595 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47429, d379595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39800 q selected
    | true =>
      simp only [d47429, d379595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47430 q = 0) : d379596 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47430, d379596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47430, d379596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47431 q = 0) : d379597 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47431, d379597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47431, d379597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47432 q = 0) : d379598 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47432, d379598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47432, d379598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47433 q = 0) : d379599 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47433, d379599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47433, d379599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47434 q = 0) : d379600 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47434, d379600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47434, d379600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39802 (p : Pattern) (selected : d47440 p = 0) : d379606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47435 q = 0) : d379601 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47435, d379601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39801 q selected
    | true =>
      simp only [d47435, d379601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47436 q = 0) : d379602 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47436, d379602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47436, d379602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47437 q = 0) : d379603 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47437, d379603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47437, d379603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47438 q = 0) : d379604 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47438, d379604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47438, d379604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47439 q = 0) : d379605 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47439, d379605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47439, d379605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47440 q = 0) : d379606 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47440, d379606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47440, d379606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39803 (p : Pattern) (selected : d47446 p = 0) : d379612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47441 q = 0) : d379607 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47441, d379607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39802 q selected
    | true =>
      simp only [d47441, d379607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47442 q = 0) : d379608 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47442, d379608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47442, d379608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47443 q = 0) : d379609 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47443, d379609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47443, d379609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47444 q = 0) : d379610 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47444, d379610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47444, d379610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47445 q = 0) : d379611 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47445, d379611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47445, d379611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47446 q = 0) : d379612 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47446, d379612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47446, d379612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39804 (p : Pattern) (selected : d47452 p = 0) : d379618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47447 q = 0) : d379613 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47447, d379613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39803 q selected
    | true =>
      simp only [d47447, d379613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47448 q = 0) : d379614 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47448, d379614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47448, d379614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47449 q = 0) : d379615 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47449, d379615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47449, d379615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47450 q = 0) : d379616 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47450, d379616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47450, d379616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47451 q = 0) : d379617 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47451, d379617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47451, d379617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47452 q = 0) : d379618 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47452, d379618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47452, d379618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39805 (p : Pattern) (selected : d47458 p = 0) : d379624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47453 q = 0) : d379619 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47453, d379619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39804 q selected
    | true =>
      simp only [d47453, d379619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47454 q = 0) : d379620 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47454, d379620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47454, d379620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47455 q = 0) : d379621 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47455, d379621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47455, d379621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47456 q = 0) : d379622 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47456, d379622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47456, d379622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47457 q = 0) : d379623 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47457, d379623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47457, d379623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47458 q = 0) : d379624 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47458, d379624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47458, d379624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39806 (p : Pattern) (selected : d47464 p = 0) : d379630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47459 q = 0) : d379625 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47459, d379625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39805 q selected
    | true =>
      simp only [d47459, d379625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47460 q = 0) : d379626 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47460, d379626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47460, d379626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47461 q = 0) : d379627 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47461, d379627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47461, d379627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47462 q = 0) : d379628 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47462, d379628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47462, d379628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47463 q = 0) : d379629 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47463, d379629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47463, d379629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47464 q = 0) : d379630 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47464, d379630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47464, d379630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39807 (p : Pattern) (selected : d47375 p = 2) : d379373 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 2) : d367652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38350 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d45903 q = 2) : d367679 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d367679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38427 q selected
  have h3 (q : Pattern) (selected : d45904 q = 2) : d367680 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d367680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47372 q = 2) : d379370 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47372, d379370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47372, d379370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47373 q = 2) : d379371 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47373, d379371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47373, d379371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47374 q = 2) : d379372 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47374, d379372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47374, d379372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d47375 q = 2) : d379373 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47375, d379373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47375, d379373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro39808 (p : Pattern) (selected : d47381 p = 2) : d379379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47376 q = 2) : d379374 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47376, d379374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39807 q selected
    | true =>
      simp only [d47376, d379374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47377 q = 2) : d379375 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47377, d379375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47377, d379375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47378 q = 2) : d379376 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47378, d379376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47378, d379376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47379 q = 2) : d379377 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47379, d379377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47379, d379377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47380 q = 2) : d379378 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47380, d379378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47380, d379378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47381 q = 2) : d379379 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47381, d379379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47381, d379379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39809 (p : Pattern) (selected : d47387 p = 2) : d379385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47382 q = 2) : d379380 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47382, d379380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39808 q selected
    | true =>
      simp only [d47382, d379380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47383 q = 2) : d379381 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47383, d379381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47383, d379381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47384 q = 2) : d379382 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47384, d379382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47384, d379382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47385 q = 2) : d379383 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47385, d379383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47385, d379383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47386 q = 2) : d379384 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47386, d379384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47386, d379384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47387 q = 2) : d379385 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47387, d379385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47387, d379385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39810 (p : Pattern) (selected : d47393 p = 2) : d379391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47388 q = 2) : d379386 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47388, d379386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39809 q selected
    | true =>
      simp only [d47388, d379386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47389 q = 2) : d379387 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47389, d379387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47389, d379387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47390 q = 2) : d379388 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47390, d379388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47390, d379388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47391 q = 2) : d379389 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47391, d379389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47391, d379389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47392 q = 2) : d379390 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47392, d379390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47392, d379390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47393 q = 2) : d379391 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47393, d379391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47393, d379391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39811 (p : Pattern) (selected : d47399 p = 2) : d379397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47394 q = 2) : d379392 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47394, d379392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39810 q selected
    | true =>
      simp only [d47394, d379392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47395 q = 2) : d379393 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47395, d379393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47395, d379393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47396 q = 2) : d379394 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47396, d379394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47396, d379394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47397 q = 2) : d379395 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47397, d379395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47397, d379395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47398 q = 2) : d379396 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47398, d379396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47398, d379396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47399 q = 2) : d379397 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47399, d379397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47399, d379397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39812 (p : Pattern) (selected : d47405 p = 2) : d379403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47400 q = 2) : d379398 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47400, d379398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39811 q selected
    | true =>
      simp only [d47400, d379398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47401 q = 2) : d379399 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47401, d379399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47401, d379399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47402 q = 2) : d379400 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47402, d379400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47402, d379400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47403 q = 2) : d379401 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47403, d379401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47403, d379401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47404 q = 2) : d379402 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47404, d379402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47404, d379402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47405 q = 2) : d379403 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47405, d379403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47405, d379403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39813 (p : Pattern) (selected : d47411 p = 2) : d379409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47406 q = 2) : d379404 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47406, d379404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39812 q selected
    | true =>
      simp only [d47406, d379404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47407 q = 2) : d379405 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47407, d379405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47407, d379405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47408 q = 2) : d379406 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47408, d379406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47408, d379406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47409 q = 2) : d379407 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47409, d379407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47409, d379407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47410 q = 2) : d379408 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47410, d379408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47410, d379408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47411 q = 2) : d379409 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47411, d379409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47411, d379409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39814 (p : Pattern) (selected : d47417 p = 2) : d379415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47412 q = 2) : d379410 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47412, d379410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39813 q selected
    | true =>
      simp only [d47412, d379410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47413 q = 2) : d379411 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47413, d379411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47413, d379411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47414 q = 2) : d379412 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47414, d379412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47414, d379412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47415 q = 2) : d379413 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47415, d379413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47415, d379413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47416 q = 2) : d379414 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47416, d379414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47416, d379414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47417 q = 2) : d379415 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47417, d379415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47417, d379415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39815 (p : Pattern) (selected : d47422 p = 1) : d379635 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d47418 q = 1) : d379631 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47418, d379631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47418, d379631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47419 q = 1) : d379632 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47419, d379632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47419, d379632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d47420 q = 1) : d379633 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47420, d379633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47420, d379633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47421 q = 1) : d379634 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47421, d379634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47421, d379634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47422 q = 1) : d379635 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47422, d379635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47422, d379635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39816 (p : Pattern) (selected : d47428 p = 1) : d379641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47423 q = 1) : d379636 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47423, d379636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39815 q selected
    | true =>
      simp only [d47423, d379636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47424 q = 1) : d379637 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47424, d379637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47424, d379637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47425 q = 1) : d379638 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47425, d379638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47425, d379638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47426 q = 1) : d379639 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47426, d379639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47426, d379639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47427 q = 1) : d379640 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47427, d379640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47427, d379640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47428 q = 1) : d379641 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47428, d379641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47428, d379641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39817 (p : Pattern) (selected : d47434 p = 1) : d379647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47429 q = 1) : d379642 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47429, d379642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39816 q selected
    | true =>
      simp only [d47429, d379642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47430 q = 1) : d379643 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47430, d379643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47430, d379643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47431 q = 1) : d379644 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47431, d379644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47431, d379644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47432 q = 1) : d379645 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47432, d379645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47432, d379645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47433 q = 1) : d379646 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47433, d379646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47433, d379646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47434 q = 1) : d379647 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47434, d379647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47434, d379647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39818 (p : Pattern) (selected : d47440 p = 1) : d379653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47435 q = 1) : d379648 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47435, d379648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39817 q selected
    | true =>
      simp only [d47435, d379648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47436 q = 1) : d379649 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47436, d379649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47436, d379649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47437 q = 1) : d379650 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47437, d379650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47437, d379650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47438 q = 1) : d379651 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47438, d379651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47438, d379651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47439 q = 1) : d379652 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47439, d379652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47439, d379652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47440 q = 1) : d379653 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47440, d379653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47440, d379653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39819 (p : Pattern) (selected : d47446 p = 1) : d379659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47441 q = 1) : d379654 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47441, d379654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39818 q selected
    | true =>
      simp only [d47441, d379654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47442 q = 1) : d379655 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47442, d379655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47442, d379655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47443 q = 1) : d379656 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47443, d379656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47443, d379656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47444 q = 1) : d379657 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47444, d379657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47444, d379657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47445 q = 1) : d379658 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47445, d379658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47445, d379658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47446 q = 1) : d379659 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47446, d379659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47446, d379659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39820 (p : Pattern) (selected : d47452 p = 1) : d379665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47447 q = 1) : d379660 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47447, d379660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39819 q selected
    | true =>
      simp only [d47447, d379660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47448 q = 1) : d379661 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47448, d379661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47448, d379661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47449 q = 1) : d379662 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47449, d379662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47449, d379662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47450 q = 1) : d379663 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47450, d379663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47450, d379663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47451 q = 1) : d379664 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47451, d379664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47451, d379664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47452 q = 1) : d379665 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47452, d379665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47452, d379665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39821 (p : Pattern) (selected : d47458 p = 1) : d379671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47453 q = 1) : d379666 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47453, d379666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39820 q selected
    | true =>
      simp only [d47453, d379666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47454 q = 1) : d379667 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47454, d379667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47454, d379667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47455 q = 1) : d379668 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47455, d379668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47455, d379668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47456 q = 1) : d379669 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47456, d379669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47456, d379669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47457 q = 1) : d379670 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47457, d379670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47457, d379670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47458 q = 1) : d379671 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47458, d379671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47458, d379671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39822 (p : Pattern) (selected : d47464 p = 1) : d379677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47459 q = 1) : d379672 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47459, d379672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39821 q selected
    | true =>
      simp only [d47459, d379672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47460 q = 1) : d379673 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47460, d379673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47460, d379673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47461 q = 1) : d379674 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47461, d379674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47461, d379674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47462 q = 1) : d379675 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47462, d379675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47462, d379675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47463 q = 1) : d379676 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47463, d379676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47463, d379676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47464 q = 1) : d379677 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47464, d379677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47464, d379677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39823 (p : Pattern) (selected : d379738 p = 0) : d379784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379734 q = 0) : d379780 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379734, d379780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d379734, d379780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379735 q = 0) : d379781 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379735, d379781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379735, d379781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379736 q = 0) : d379782 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379736, d379782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379736, d379782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379737 q = 0) : d379783 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379737, d379783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379737, d379783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379738 q = 0) : d379784 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379738, d379784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379738, d379784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39824 (p : Pattern) (selected : d379744 p = 0) : d379790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379739 q = 0) : d379785 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379739, d379785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39823 q selected
    | true =>
      simp only [d379739, d379785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379740 q = 0) : d379786 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379740, d379786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379740, d379786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379741 q = 0) : d379787 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379741, d379787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379741, d379787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379742 q = 0) : d379788 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379742, d379788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379742, d379788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379743 q = 0) : d379789 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379743, d379789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379743, d379789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379744 q = 0) : d379790 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379744, d379790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379744, d379790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39825 (p : Pattern) (selected : d379749 p = 0) : d379795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379745 q = 0) : d379791 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379745, d379791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39824 q selected
    | true =>
      simp only [d379745, d379791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379746 q = 0) : d379792 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379746, d379792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379746, d379792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379747 q = 0) : d379793 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379747, d379793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379747, d379793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379748 q = 0) : d379794 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379748, d379794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379748, d379794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379749 q = 0) : d379795 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379749, d379795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379749, d379795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39826 (p : Pattern) (selected : d379755 p = 0) : d379801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379750 q = 0) : d379796 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379750, d379796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39825 q selected
    | true =>
      simp only [d379750, d379796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379751 q = 0) : d379797 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379751, d379797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379751, d379797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379752 q = 0) : d379798 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379752, d379798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379752, d379798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379753 q = 0) : d379799 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379753, d379799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379753, d379799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379754 q = 0) : d379800 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379754, d379800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379754, d379800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379755 q = 0) : d379801 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379755, d379801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379755, d379801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39827 (p : Pattern) (selected : d379761 p = 0) : d379807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379756 q = 0) : d379802 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379756, d379802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39826 q selected
    | true =>
      simp only [d379756, d379802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379757 q = 0) : d379803 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379757, d379803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379757, d379803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379758 q = 0) : d379804 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379758, d379804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379758, d379804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379759 q = 0) : d379805 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379759, d379805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379759, d379805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379760 q = 0) : d379806 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379760, d379806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379760, d379806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379761 q = 0) : d379807 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379761, d379807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379761, d379807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39828 (p : Pattern) (selected : d379767 p = 0) : d379813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379762 q = 0) : d379808 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379762, d379808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39827 q selected
    | true =>
      simp only [d379762, d379808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379763 q = 0) : d379809 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379763, d379809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379763, d379809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379764 q = 0) : d379810 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379764, d379810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379764, d379810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379765 q = 0) : d379811 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379765, d379811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379765, d379811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379766 q = 0) : d379812 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379766, d379812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379766, d379812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379767 q = 0) : d379813 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379767, d379813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379767, d379813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39829 (p : Pattern) (selected : d379773 p = 0) : d379819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379768 q = 0) : d379814 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379768, d379814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39828 q selected
    | true =>
      simp only [d379768, d379814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379769 q = 0) : d379815 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379769, d379815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379769, d379815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379770 q = 0) : d379816 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379770, d379816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379770, d379816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379771 q = 0) : d379817 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379771, d379817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379771, d379817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379772 q = 0) : d379818 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379772, d379818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379772, d379818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379773 q = 0) : d379819 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379773, d379819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379773, d379819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39830 (p : Pattern) (selected : d379779 p = 0) : d379825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379774 q = 0) : d379820 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379774, d379820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39829 q selected
    | true =>
      simp only [d379774, d379820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379775 q = 0) : d379821 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379775, d379821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379775, d379821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379776 q = 0) : d379822 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379776, d379822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379776, d379822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379777 q = 0) : d379823 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379777, d379823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379777, d379823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379778 q = 0) : d379824 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379778, d379824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379778, d379824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379779 q = 0) : d379825 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379779, d379825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379779, d379825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39831 (p : Pattern) (selected : d379738 p = 1) : d379830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379734 q = 1) : d379826 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379734, d379826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d379734, d379826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379735 q = 1) : d379827 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379735, d379827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379735, d379827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379736 q = 1) : d379828 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379736, d379828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379736, d379828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379737 q = 1) : d379829 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379737, d379829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379737, d379829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379738 q = 1) : d379830 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379738, d379830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379738, d379830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39832 (p : Pattern) (selected : d379744 p = 1) : d379836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379739 q = 1) : d379831 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379739, d379831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39831 q selected
    | true =>
      simp only [d379739, d379831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379740 q = 1) : d379832 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379740, d379832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379740, d379832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379741 q = 1) : d379833 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379741, d379833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379741, d379833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379742 q = 1) : d379834 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379742, d379834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379742, d379834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379743 q = 1) : d379835 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379743, d379835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379743, d379835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379744 q = 1) : d379836 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379744, d379836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379744, d379836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39833 (p : Pattern) (selected : d379749 p = 1) : d379841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379745 q = 1) : d379837 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379745, d379837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39832 q selected
    | true =>
      simp only [d379745, d379837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379746 q = 1) : d379838 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379746, d379838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379746, d379838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379747 q = 1) : d379839 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379747, d379839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379747, d379839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379748 q = 1) : d379840 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379748, d379840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379748, d379840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379749 q = 1) : d379841 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379749, d379841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379749, d379841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39834 (p : Pattern) (selected : d379755 p = 1) : d379847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379750 q = 1) : d379842 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379750, d379842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39833 q selected
    | true =>
      simp only [d379750, d379842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379751 q = 1) : d379843 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379751, d379843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379751, d379843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379752 q = 1) : d379844 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379752, d379844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379752, d379844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379753 q = 1) : d379845 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379753, d379845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379753, d379845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379754 q = 1) : d379846 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379754, d379846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379754, d379846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379755 q = 1) : d379847 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379755, d379847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379755, d379847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39835 (p : Pattern) (selected : d379761 p = 1) : d379853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379756 q = 1) : d379848 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379756, d379848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39834 q selected
    | true =>
      simp only [d379756, d379848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379757 q = 1) : d379849 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379757, d379849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379757, d379849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379758 q = 1) : d379850 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379758, d379850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379758, d379850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379759 q = 1) : d379851 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379759, d379851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379759, d379851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379760 q = 1) : d379852 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379760, d379852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379760, d379852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379761 q = 1) : d379853 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379761, d379853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379761, d379853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39836 (p : Pattern) (selected : d379767 p = 1) : d379859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379762 q = 1) : d379854 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379762, d379854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39835 q selected
    | true =>
      simp only [d379762, d379854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379763 q = 1) : d379855 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379763, d379855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379763, d379855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379764 q = 1) : d379856 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379764, d379856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379764, d379856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379765 q = 1) : d379857 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379765, d379857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379765, d379857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379766 q = 1) : d379858 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379766, d379858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379766, d379858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379767 q = 1) : d379859 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379767, d379859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379767, d379859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39837 (p : Pattern) (selected : d379773 p = 1) : d379865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379768 q = 1) : d379860 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379768, d379860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39836 q selected
    | true =>
      simp only [d379768, d379860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379769 q = 1) : d379861 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379769, d379861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379769, d379861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379770 q = 1) : d379862 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379770, d379862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379770, d379862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379771 q = 1) : d379863 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379771, d379863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379771, d379863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379772 q = 1) : d379864 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379772, d379864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379772, d379864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379773 q = 1) : d379865 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379773, d379865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379773, d379865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39838 (p : Pattern) (selected : d379779 p = 1) : d379871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379774 q = 1) : d379866 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379774, d379866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39837 q selected
    | true =>
      simp only [d379774, d379866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379775 q = 1) : d379867 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379775, d379867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379775, d379867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379776 q = 1) : d379868 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379776, d379868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379776, d379868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379777 q = 1) : d379869 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379777, d379869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379777, d379869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379778 q = 1) : d379870 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379778, d379870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379778, d379870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379779 q = 1) : d379871 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379779, d379871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379779, d379871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39839 (p : Pattern) (selected : d379883 p = 0) : d379925 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 0) : d319887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d319887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33272 q selected
  have h5 (q : Pattern) (selected : d46457 q = 0) : d319888 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d319888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 0) : d319889 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d319889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47327 q = 0) : d378992 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47327, d378992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47327, d378992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d379883 q = 0) : d379925 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379883, d379925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d379883, d379925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro39840 (p : Pattern) (selected : d379889 p = 0) : d379931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379884 q = 0) : d379926 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379884, d379926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39839 q selected
    | true =>
      simp only [d379884, d379926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379885 q = 0) : d379927 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379885, d379927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379885, d379927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379886 q = 0) : d379928 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379886, d379928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379886, d379928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379887 q = 0) : d379929 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379887, d379929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379887, d379929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379888 q = 0) : d379930 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379888, d379930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379888, d379930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379889 q = 0) : d379931 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379889, d379931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379889, d379931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39841 (p : Pattern) (selected : d379894 p = 0) : d379936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379890 q = 0) : d379932 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379890, d379932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39840 q selected
    | true =>
      simp only [d379890, d379932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379891 q = 0) : d379933 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379891, d379933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379891, d379933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379892 q = 0) : d379934 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379892, d379934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379892, d379934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379893 q = 0) : d379935 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379893, d379935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379893, d379935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379894 q = 0) : d379936 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379894, d379936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379894, d379936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39842 (p : Pattern) (selected : d379900 p = 0) : d379942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379895 q = 0) : d379937 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379895, d379937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39841 q selected
    | true =>
      simp only [d379895, d379937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379896 q = 0) : d379938 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379896, d379938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379896, d379938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379897 q = 0) : d379939 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379897, d379939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379897, d379939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379898 q = 0) : d379940 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379898, d379940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379898, d379940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379899 q = 0) : d379941 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379899, d379941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379899, d379941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379900 q = 0) : d379942 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379900, d379942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379900, d379942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39843 (p : Pattern) (selected : d379906 p = 0) : d379948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379901 q = 0) : d379943 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379901, d379943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39842 q selected
    | true =>
      simp only [d379901, d379943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379902 q = 0) : d379944 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379902, d379944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379902, d379944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379903 q = 0) : d379945 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379903, d379945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379903, d379945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379904 q = 0) : d379946 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379904, d379946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379904, d379946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379905 q = 0) : d379947 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379905, d379947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379905, d379947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379906 q = 0) : d379948 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379906, d379948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379906, d379948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39844 (p : Pattern) (selected : d379912 p = 0) : d379954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379907 q = 0) : d379949 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379907, d379949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39843 q selected
    | true =>
      simp only [d379907, d379949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379908 q = 0) : d379950 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379908, d379950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379908, d379950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379909 q = 0) : d379951 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379909, d379951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379909, d379951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379910 q = 0) : d379952 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379910, d379952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379910, d379952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379911 q = 0) : d379953 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379911, d379953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379911, d379953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379912 q = 0) : d379954 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379912, d379954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379912, d379954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39845 (p : Pattern) (selected : d379918 p = 0) : d379960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379913 q = 0) : d379955 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379913, d379955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39844 q selected
    | true =>
      simp only [d379913, d379955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379914 q = 0) : d379956 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379914, d379956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379914, d379956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379915 q = 0) : d379957 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379915, d379957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379915, d379957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379916 q = 0) : d379958 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379916, d379958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379916, d379958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379917 q = 0) : d379959 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379917, d379959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379917, d379959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379918 q = 0) : d379960 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379918, d379960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379918, d379960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39846 (p : Pattern) (selected : d379924 p = 0) : d379966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d379919 q = 0) : d379961 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379919, d379961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39845 q selected
    | true =>
      simp only [d379919, d379961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379920 q = 0) : d379962 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379920, d379962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379920, d379962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379921 q = 0) : d379963 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379921, d379963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379921, d379963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379922 q = 0) : d379964 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379922, d379964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379922, d379964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379923 q = 0) : d379965 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379923, d379965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379923, d379965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379924 q = 0) : d379966 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379924, d379966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379924, d379966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39847 (p : Pattern) (selected : d379883 p = 1) : d379967 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d46456 q = 1) : d322203 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46456, d322203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33532 q selected
  have h5 (q : Pattern) (selected : d46457 q = 1) : d322204 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d46457, d322204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d46458 q = 1) : d322205 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d46458, d322205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47327 q = 1) : d379037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47327, d379037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47327, d379037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d379883 q = 1) : d379967 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379883, d379967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d379883, d379967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro39848 (p : Pattern) (selected : d379889 p = 1) : d379973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379884 q = 1) : d379968 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379884, d379968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39847 q selected
    | true =>
      simp only [d379884, d379968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379885 q = 1) : d379969 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379885, d379969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379885, d379969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379886 q = 1) : d379970 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379886, d379970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379886, d379970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379887 q = 1) : d379971 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379887, d379971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379887, d379971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379888 q = 1) : d379972 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379888, d379972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379888, d379972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379889 q = 1) : d379973 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379889, d379973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379889, d379973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39849 (p : Pattern) (selected : d379894 p = 1) : d379978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379890 q = 1) : d379974 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379890, d379974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39848 q selected
    | true =>
      simp only [d379890, d379974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379891 q = 1) : d379975 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379891, d379975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379891, d379975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379892 q = 1) : d379976 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379892, d379976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379892, d379976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379893 q = 1) : d379977 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379893, d379977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379893, d379977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379894 q = 1) : d379978 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379894, d379978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379894, d379978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39850 (p : Pattern) (selected : d379900 p = 1) : d379984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379895 q = 1) : d379979 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379895, d379979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39849 q selected
    | true =>
      simp only [d379895, d379979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379896 q = 1) : d379980 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379896, d379980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379896, d379980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379897 q = 1) : d379981 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379897, d379981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379897, d379981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379898 q = 1) : d379982 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379898, d379982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379898, d379982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379899 q = 1) : d379983 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379899, d379983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379899, d379983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379900 q = 1) : d379984 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379900, d379984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379900, d379984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39851 (p : Pattern) (selected : d379906 p = 1) : d379990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379901 q = 1) : d379985 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379901, d379985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39850 q selected
    | true =>
      simp only [d379901, d379985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379902 q = 1) : d379986 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379902, d379986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379902, d379986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379903 q = 1) : d379987 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379903, d379987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379903, d379987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379904 q = 1) : d379988 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379904, d379988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379904, d379988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379905 q = 1) : d379989 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379905, d379989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379905, d379989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379906 q = 1) : d379990 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379906, d379990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379906, d379990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39852 (p : Pattern) (selected : d379912 p = 1) : d379996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379907 q = 1) : d379991 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379907, d379991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39851 q selected
    | true =>
      simp only [d379907, d379991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379908 q = 1) : d379992 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379908, d379992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379908, d379992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379909 q = 1) : d379993 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379909, d379993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379909, d379993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379910 q = 1) : d379994 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379910, d379994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379910, d379994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379911 q = 1) : d379995 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379911, d379995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379911, d379995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379912 q = 1) : d379996 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379912, d379996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379912, d379996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39853 (p : Pattern) (selected : d379918 p = 1) : d380002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379913 q = 1) : d379997 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379913, d379997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39852 q selected
    | true =>
      simp only [d379913, d379997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379914 q = 1) : d379998 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379914, d379998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379914, d379998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379915 q = 1) : d379999 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379915, d379999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379915, d379999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379916 q = 1) : d380000 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379916, d380000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379916, d380000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379917 q = 1) : d380001 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379917, d380001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379917, d380001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379918 q = 1) : d380002 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379918, d380002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379918, d380002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39854 (p : Pattern) (selected : d379924 p = 1) : d380008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d379919 q = 1) : d380003 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379919, d380003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39853 q selected
    | true =>
      simp only [d379919, d380003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d379920 q = 1) : d380004 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379920, d380004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d379920, d380004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d379921 q = 1) : d380005 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379921, d380005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d379921, d380005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d379922 q = 1) : d380006 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379922, d380006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d379922, d380006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d379923 q = 1) : d380007 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379923, d380007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d379923, d380007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d379924 q = 1) : d380008 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379924, d380008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d379924, d380008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39855 (p : Pattern) (selected : d47470 p = 0) : d380020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47465 q = 0) : d380015 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47465, d380015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d47465, d380015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47466 q = 0) : d380016 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47466, d380016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47466, d380016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47467 q = 0) : d380017 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47467, d380017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47467, d380017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47468 q = 0) : d380018 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47468, d380018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47468, d380018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47469 q = 0) : d380019 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47469, d380019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47469, d380019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47470 q = 0) : d380020 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47470, d380020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47470, d380020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39856 (p : Pattern) (selected : d47476 p = 0) : d380026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47471 q = 0) : d380021 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47471, d380021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39855 q selected
    | true =>
      simp only [d47471, d380021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47472 q = 0) : d380022 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47472, d380022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47472, d380022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47473 q = 0) : d380023 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47473, d380023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47473, d380023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47474 q = 0) : d380024 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47474, d380024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47474, d380024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47475 q = 0) : d380025 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47475, d380025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47475, d380025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47476 q = 0) : d380026 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47476, d380026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47476, d380026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39857 (p : Pattern) (selected : d47482 p = 0) : d380032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47477 q = 0) : d380027 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47477, d380027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39856 q selected
    | true =>
      simp only [d47477, d380027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47478 q = 0) : d380028 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47478, d380028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47478, d380028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47479 q = 0) : d380029 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47479, d380029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47479, d380029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47480 q = 0) : d380030 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47480, d380030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47480, d380030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47481 q = 0) : d380031 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47481, d380031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47481, d380031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47482 q = 0) : d380032 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47482, d380032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47482, d380032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39858 (p : Pattern) (selected : d47488 p = 0) : d380038 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47483 q = 0) : d380033 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47483, d380033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39857 q selected
    | true =>
      simp only [d47483, d380033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47484 q = 0) : d380034 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47484, d380034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47484, d380034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47485 q = 0) : d380035 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47485, d380035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47485, d380035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47486 q = 0) : d380036 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47486, d380036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47486, d380036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47487 q = 0) : d380037 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47487, d380037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47487, d380037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47488 q = 0) : d380038 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47488, d380038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47488, d380038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39859 (p : Pattern) (selected : d47494 p = 0) : d380044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47489 q = 0) : d380039 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47489, d380039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39858 q selected
    | true =>
      simp only [d47489, d380039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47490 q = 0) : d380040 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47490, d380040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47490, d380040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47491 q = 0) : d380041 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47491, d380041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47491, d380041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47492 q = 0) : d380042 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47492, d380042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47492, d380042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47493 q = 0) : d380043 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47493, d380043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47493, d380043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47494 q = 0) : d380044 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47494, d380044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47494, d380044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39860 (p : Pattern) (selected : d47500 p = 0) : d380050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47495 q = 0) : d380045 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47495, d380045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39859 q selected
    | true =>
      simp only [d47495, d380045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47496 q = 0) : d380046 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47496, d380046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47496, d380046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47497 q = 0) : d380047 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47497, d380047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47497, d380047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47498 q = 0) : d380048 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47498, d380048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47498, d380048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47499 q = 0) : d380049 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47499, d380049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47499, d380049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47500 q = 0) : d380050 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47500, d380050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47500, d380050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39861 (p : Pattern) (selected : d47506 p = 0) : d380056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47501 q = 0) : d380051 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47501, d380051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39860 q selected
    | true =>
      simp only [d47501, d380051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47502 q = 0) : d380052 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47502, d380052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47502, d380052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47503 q = 0) : d380053 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47503, d380053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47503, d380053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47504 q = 0) : d380054 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47504, d380054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47504, d380054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47505 q = 0) : d380055 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47505, d380055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47505, d380055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47506 q = 0) : d380056 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47506, d380056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47506, d380056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39862 (p : Pattern) (selected : d47512 p = 0) : d380062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47507 q = 0) : d380057 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47507, d380057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39861 q selected
    | true =>
      simp only [d47507, d380057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47508 q = 0) : d380058 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47508, d380058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47508, d380058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47509 q = 0) : d380059 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47509, d380059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47509, d380059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47510 q = 0) : d380060 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47510, d380060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47510, d380060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47511 q = 0) : d380061 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47511, d380061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47511, d380061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47512 q = 0) : d380062 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47512, d380062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47512, d380062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39863 (p : Pattern) (selected : d47422 p = 2) : d379682 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 2) : d367652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d45496, d367652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38350 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d47418 q = 2) : d379678 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47418, d379678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47418, d379678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d47419 q = 2) : d379679 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47419, d379679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47419, d379679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d47420 q = 2) : d379680 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47420, d379680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47420, d379680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d47421 q = 2) : d379681 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47421, d379681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47421, d379681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d47422 q = 2) : d379682 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47422, d379682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47422, d379682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39864 (p : Pattern) (selected : d47428 p = 2) : d379688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47423 q = 2) : d379683 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47423, d379683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39863 q selected
    | true =>
      simp only [d47423, d379683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47424 q = 2) : d379684 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47424, d379684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47424, d379684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47425 q = 2) : d379685 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47425, d379685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47425, d379685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47426 q = 2) : d379686 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47426, d379686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47426, d379686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47427 q = 2) : d379687 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47427, d379687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47427, d379687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47428 q = 2) : d379688 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47428, d379688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47428, d379688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39865 (p : Pattern) (selected : d47434 p = 2) : d379694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47429 q = 2) : d379689 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47429, d379689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39864 q selected
    | true =>
      simp only [d47429, d379689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47430 q = 2) : d379690 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47430, d379690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47430, d379690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47431 q = 2) : d379691 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47431, d379691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47431, d379691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47432 q = 2) : d379692 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47432, d379692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47432, d379692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47433 q = 2) : d379693 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47433, d379693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47433, d379693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47434 q = 2) : d379694 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47434, d379694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47434, d379694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39866 (p : Pattern) (selected : d47440 p = 2) : d379700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47435 q = 2) : d379695 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47435, d379695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39865 q selected
    | true =>
      simp only [d47435, d379695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47436 q = 2) : d379696 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47436, d379696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47436, d379696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47437 q = 2) : d379697 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47437, d379697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47437, d379697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47438 q = 2) : d379698 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47438, d379698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47438, d379698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47439 q = 2) : d379699 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47439, d379699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47439, d379699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47440 q = 2) : d379700 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47440, d379700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47440, d379700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39867 (p : Pattern) (selected : d47446 p = 2) : d379706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47441 q = 2) : d379701 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47441, d379701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39866 q selected
    | true =>
      simp only [d47441, d379701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47442 q = 2) : d379702 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47442, d379702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47442, d379702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47443 q = 2) : d379703 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47443, d379703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47443, d379703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47444 q = 2) : d379704 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47444, d379704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47444, d379704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47445 q = 2) : d379705 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47445, d379705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47445, d379705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47446 q = 2) : d379706 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47446, d379706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47446, d379706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39868 (p : Pattern) (selected : d47452 p = 2) : d379712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47447 q = 2) : d379707 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47447, d379707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39867 q selected
    | true =>
      simp only [d47447, d379707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47448 q = 2) : d379708 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47448, d379708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47448, d379708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47449 q = 2) : d379709 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47449, d379709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47449, d379709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47450 q = 2) : d379710 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47450, d379710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47450, d379710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47451 q = 2) : d379711 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47451, d379711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47451, d379711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47452 q = 2) : d379712 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47452, d379712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47452, d379712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39869 (p : Pattern) (selected : d47458 p = 2) : d379718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47453 q = 2) : d379713 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47453, d379713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39868 q selected
    | true =>
      simp only [d47453, d379713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47454 q = 2) : d379714 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47454, d379714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47454, d379714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47455 q = 2) : d379715 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47455, d379715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47455, d379715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47456 q = 2) : d379716 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47456, d379716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47456, d379716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47457 q = 2) : d379717 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47457, d379717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47457, d379717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47458 q = 2) : d379718 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47458, d379718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47458, d379718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39870 (p : Pattern) (selected : d47464 p = 2) : d379724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47459 q = 2) : d379719 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47459, d379719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39869 q selected
    | true =>
      simp only [d47459, d379719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47460 q = 2) : d379720 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47460, d379720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47460, d379720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47461 q = 2) : d379721 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47461, d379721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47461, d379721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47462 q = 2) : d379722 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47462, d379722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47462, d379722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47463 q = 2) : d379723 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47463, d379723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47463, d379723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47464 q = 2) : d379724 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47464, d379724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47464, d379724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39871 (p : Pattern) (selected : d47470 p = 1) : d380068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47465 q = 1) : d380063 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47465, d380063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d47465, d380063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47466 q = 1) : d380064 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47466, d380064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47466, d380064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47467 q = 1) : d380065 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47467, d380065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47467, d380065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47468 q = 1) : d380066 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47468, d380066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47468, d380066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47469 q = 1) : d380067 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47469, d380067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47469, d380067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47470 q = 1) : d380068 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47470, d380068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47470, d380068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39872 (p : Pattern) (selected : d47476 p = 1) : d380074 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47471 q = 1) : d380069 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47471, d380069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39871 q selected
    | true =>
      simp only [d47471, d380069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47472 q = 1) : d380070 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47472, d380070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47472, d380070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47473 q = 1) : d380071 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47473, d380071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47473, d380071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47474 q = 1) : d380072 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47474, d380072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47474, d380072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47475 q = 1) : d380073 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47475, d380073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47475, d380073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47476 q = 1) : d380074 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47476, d380074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47476, d380074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39873 (p : Pattern) (selected : d47482 p = 1) : d380080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47477 q = 1) : d380075 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47477, d380075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39872 q selected
    | true =>
      simp only [d47477, d380075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47478 q = 1) : d380076 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47478, d380076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47478, d380076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47479 q = 1) : d380077 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47479, d380077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47479, d380077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47480 q = 1) : d380078 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47480, d380078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47480, d380078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47481 q = 1) : d380079 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47481, d380079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47481, d380079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47482 q = 1) : d380080 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47482, d380080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47482, d380080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39874 (p : Pattern) (selected : d47488 p = 1) : d380086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47483 q = 1) : d380081 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47483, d380081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39873 q selected
    | true =>
      simp only [d47483, d380081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47484 q = 1) : d380082 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47484, d380082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47484, d380082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47485 q = 1) : d380083 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47485, d380083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47485, d380083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47486 q = 1) : d380084 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47486, d380084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47486, d380084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47487 q = 1) : d380085 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47487, d380085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47487, d380085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47488 q = 1) : d380086 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47488, d380086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47488, d380086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39875 (p : Pattern) (selected : d47494 p = 1) : d380092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47489 q = 1) : d380087 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47489, d380087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39874 q selected
    | true =>
      simp only [d47489, d380087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47490 q = 1) : d380088 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47490, d380088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47490, d380088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47491 q = 1) : d380089 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47491, d380089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47491, d380089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47492 q = 1) : d380090 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47492, d380090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47492, d380090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47493 q = 1) : d380091 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47493, d380091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47493, d380091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47494 q = 1) : d380092 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47494, d380092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47494, d380092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39876 (p : Pattern) (selected : d47500 p = 1) : d380098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47495 q = 1) : d380093 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47495, d380093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39875 q selected
    | true =>
      simp only [d47495, d380093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47496 q = 1) : d380094 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47496, d380094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47496, d380094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47497 q = 1) : d380095 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47497, d380095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47497, d380095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47498 q = 1) : d380096 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47498, d380096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47498, d380096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47499 q = 1) : d380097 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47499, d380097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47499, d380097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47500 q = 1) : d380098 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47500, d380098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47500, d380098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39877 (p : Pattern) (selected : d47506 p = 1) : d380104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47501 q = 1) : d380099 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47501, d380099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39876 q selected
    | true =>
      simp only [d47501, d380099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47502 q = 1) : d380100 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47502, d380100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47502, d380100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47503 q = 1) : d380101 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47503, d380101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47503, d380101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47504 q = 1) : d380102 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47504, d380102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47504, d380102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47505 q = 1) : d380103 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47505, d380103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47505, d380103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47506 q = 1) : d380104 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47506, d380104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47506, d380104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39878 (p : Pattern) (selected : d47512 p = 1) : d380110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47507 q = 1) : d380105 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47507, d380105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39877 q selected
    | true =>
      simp only [d47507, d380105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47508 q = 1) : d380106 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47508, d380106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47508, d380106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47509 q = 1) : d380107 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47509, d380107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47509, d380107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47510 q = 1) : d380108 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47510, d380108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47510, d380108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47511 q = 1) : d380109 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47511, d380109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47511, d380109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47512 q = 1) : d380110 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47512, d380110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47512, d380110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39879 (p : Pattern) (selected : d44968 p = 0) : d318813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44964 q = 0) : d318809 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d318809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44964, d318809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33010 q selected
  have h6 (q : Pattern) (selected : d44965 q = 0) : d318810 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d318810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44965, d318810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44966 q = 0) : d318811 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d318811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44966, d318811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44967 q = 0) : d318812 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d318812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44967, d318812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44968 q = 0) : d318813 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d318813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44968, d318813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro39880 (p : Pattern) (selected : d380173 p = 0) : d380220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380168 q = 0) : d380215 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380168, d380215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39879 q selected
    | true =>
      simp only [d380168, d380215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380169 q = 0) : d380216 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380169, d380216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380169, d380216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380170 q = 0) : d380217 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380170, d380217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380170, d380217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380171 q = 0) : d380218 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380171, d380218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380171, d380218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380172 q = 0) : d380219 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380172, d380219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380172, d380219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380173 q = 0) : d380220 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380173, d380220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380173, d380220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39881 (p : Pattern) (selected : d380178 p = 0) : d380225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380174 q = 0) : d380221 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380174, d380221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39880 q selected
    | true =>
      simp only [d380174, d380221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380175 q = 0) : d380222 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380175, d380222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380175, d380222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380176 q = 0) : d380223 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380176, d380223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380176, d380223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380177 q = 0) : d380224 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380177, d380224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380177, d380224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380178 q = 0) : d380225 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380178, d380225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380178, d380225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39882 (p : Pattern) (selected : d380184 p = 0) : d380231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380179 q = 0) : d380226 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380179, d380226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39881 q selected
    | true =>
      simp only [d380179, d380226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380180 q = 0) : d380227 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380180, d380227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380180, d380227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380181 q = 0) : d380228 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380181, d380228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380181, d380228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380182 q = 0) : d380229 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380182, d380229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380182, d380229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380183 q = 0) : d380230 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380183, d380230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380183, d380230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380184 q = 0) : d380231 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380184, d380231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380184, d380231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39883 (p : Pattern) (selected : d380190 p = 0) : d380237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380185 q = 0) : d380232 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380185, d380232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39882 q selected
    | true =>
      simp only [d380185, d380232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380186 q = 0) : d380233 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380186, d380233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380186, d380233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380187 q = 0) : d380234 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380187, d380234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380187, d380234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380188 q = 0) : d380235 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380188, d380235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380188, d380235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380189 q = 0) : d380236 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380189, d380236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380189, d380236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380190 q = 0) : d380237 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380190, d380237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380190, d380237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39884 (p : Pattern) (selected : d380196 p = 0) : d380243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380191 q = 0) : d380238 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380191, d380238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39883 q selected
    | true =>
      simp only [d380191, d380238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380192 q = 0) : d380239 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380192, d380239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380192, d380239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380193 q = 0) : d380240 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380193, d380240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380193, d380240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380194 q = 0) : d380241 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380194, d380241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380194, d380241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380195 q = 0) : d380242 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380195, d380242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380195, d380242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380196 q = 0) : d380243 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380196, d380243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380196, d380243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39885 (p : Pattern) (selected : d380202 p = 0) : d380249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380197 q = 0) : d380244 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380197, d380244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39884 q selected
    | true =>
      simp only [d380197, d380244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380198 q = 0) : d380245 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380198, d380245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380198, d380245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380199 q = 0) : d380246 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380199, d380246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380199, d380246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380200 q = 0) : d380247 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380200, d380247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380200, d380247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380201 q = 0) : d380248 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380201, d380248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380201, d380248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380202 q = 0) : d380249 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380202, d380249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380202, d380249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39886 (p : Pattern) (selected : d380208 p = 0) : d380255 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380203 q = 0) : d380250 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380203, d380250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39885 q selected
    | true =>
      simp only [d380203, d380250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380204 q = 0) : d380251 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380204, d380251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380204, d380251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380205 q = 0) : d380252 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380205, d380252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380205, d380252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380206 q = 0) : d380253 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380206, d380253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380206, d380253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380207 q = 0) : d380254 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380207, d380254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380207, d380254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380208 q = 0) : d380255 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380208, d380255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380208, d380255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39887 (p : Pattern) (selected : d380214 p = 0) : d380261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380209 q = 0) : d380256 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380209, d380256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39886 q selected
    | true =>
      simp only [d380209, d380256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380210 q = 0) : d380257 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380210, d380257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380210, d380257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380211 q = 0) : d380258 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380211, d380258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380211, d380258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380212 q = 0) : d380259 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380212, d380259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380212, d380259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380213 q = 0) : d380260 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380213, d380260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380213, d380260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380214 q = 0) : d380261 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380214, d380261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380214, d380261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39888 (p : Pattern) (selected : d44968 p = 1) : d322043 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d44964 q = 1) : d322039 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33437 q selected
  have h3 (q : Pattern) (selected : d44965 q = 1) : d322040 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44966 q = 1) : d322041 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44967 q = 1) : d322042 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44968 q = 1) : d322043 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro39889 (p : Pattern) (selected : d380173 p = 1) : d380267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380168 q = 1) : d380262 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380168, d380262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39888 q selected
    | true =>
      simp only [d380168, d380262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380169 q = 1) : d380263 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380169, d380263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380169, d380263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380170 q = 1) : d380264 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380170, d380264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380170, d380264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380171 q = 1) : d380265 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380171, d380265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380171, d380265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380172 q = 1) : d380266 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380172, d380266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380172, d380266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380173 q = 1) : d380267 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380173, d380267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380173, d380267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39890 (p : Pattern) (selected : d380178 p = 1) : d380272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380174 q = 1) : d380268 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380174, d380268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39889 q selected
    | true =>
      simp only [d380174, d380268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380175 q = 1) : d380269 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380175, d380269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380175, d380269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380176 q = 1) : d380270 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380176, d380270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380176, d380270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380177 q = 1) : d380271 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380177, d380271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380177, d380271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380178 q = 1) : d380272 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380178, d380272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380178, d380272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39891 (p : Pattern) (selected : d380184 p = 1) : d380278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380179 q = 1) : d380273 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380179, d380273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39890 q selected
    | true =>
      simp only [d380179, d380273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380180 q = 1) : d380274 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380180, d380274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380180, d380274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380181 q = 1) : d380275 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380181, d380275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380181, d380275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380182 q = 1) : d380276 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380182, d380276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380182, d380276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380183 q = 1) : d380277 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380183, d380277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380183, d380277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380184 q = 1) : d380278 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380184, d380278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380184, d380278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39892 (p : Pattern) (selected : d380190 p = 1) : d380284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380185 q = 1) : d380279 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380185, d380279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39891 q selected
    | true =>
      simp only [d380185, d380279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380186 q = 1) : d380280 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380186, d380280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380186, d380280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380187 q = 1) : d380281 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380187, d380281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380187, d380281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380188 q = 1) : d380282 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380188, d380282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380188, d380282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380189 q = 1) : d380283 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380189, d380283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380189, d380283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380190 q = 1) : d380284 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380190, d380284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380190, d380284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39893 (p : Pattern) (selected : d380196 p = 1) : d380290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380191 q = 1) : d380285 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380191, d380285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39892 q selected
    | true =>
      simp only [d380191, d380285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380192 q = 1) : d380286 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380192, d380286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380192, d380286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380193 q = 1) : d380287 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380193, d380287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380193, d380287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380194 q = 1) : d380288 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380194, d380288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380194, d380288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380195 q = 1) : d380289 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380195, d380289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380195, d380289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380196 q = 1) : d380290 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380196, d380290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380196, d380290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39894 (p : Pattern) (selected : d380202 p = 1) : d380296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380197 q = 1) : d380291 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380197, d380291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39893 q selected
    | true =>
      simp only [d380197, d380291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380198 q = 1) : d380292 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380198, d380292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380198, d380292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380199 q = 1) : d380293 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380199, d380293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380199, d380293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380200 q = 1) : d380294 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380200, d380294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380200, d380294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380201 q = 1) : d380295 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380201, d380295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380201, d380295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380202 q = 1) : d380296 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380202, d380296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380202, d380296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39895 (p : Pattern) (selected : d380208 p = 1) : d380302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380203 q = 1) : d380297 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380203, d380297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39894 q selected
    | true =>
      simp only [d380203, d380297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380204 q = 1) : d380298 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380204, d380298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380204, d380298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380205 q = 1) : d380299 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380205, d380299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380205, d380299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380206 q = 1) : d380300 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380206, d380300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380206, d380300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380207 q = 1) : d380301 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380207, d380301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380207, d380301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380208 q = 1) : d380302 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380208, d380302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380208, d380302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39896 (p : Pattern) (selected : d380214 p = 1) : d380308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380209 q = 1) : d380303 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380209, d380303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39895 q selected
    | true =>
      simp only [d380209, d380303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380210 q = 1) : d380304 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380210, d380304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380210, d380304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380211 q = 1) : d380305 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380211, d380305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380211, d380305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380212 q = 1) : d380306 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380212, d380306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380212, d380306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380213 q = 1) : d380307 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380213, d380307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380213, d380307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380214 q = 1) : d380308 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380214, d380308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380214, d380308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39897 (p : Pattern) (selected : d380321 p = 0) : d380364 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d45903 q = 0) : d319500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d319500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33184 q selected
  have h3 (q : Pattern) (selected : d45904 q = 0) : d319501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d319501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47372 q = 0) : d379278 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47372, d379278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47372, d379278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d380320 q = 0) : d380363 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380320, d380363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380320, d380363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d380321 q = 0) : d380364 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380321, d380364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380321, d380364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39898 (p : Pattern) (selected : d380327 p = 0) : d380370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380322 q = 0) : d380365 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380322, d380365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39897 q selected
    | true =>
      simp only [d380322, d380365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380323 q = 0) : d380366 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380323, d380366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380323, d380366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380324 q = 0) : d380367 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380324, d380367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380324, d380367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380325 q = 0) : d380368 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380325, d380368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380325, d380368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380326 q = 0) : d380369 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380326, d380369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380326, d380369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380327 q = 0) : d380370 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380327, d380370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380327, d380370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39899 (p : Pattern) (selected : d380332 p = 0) : d380375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380328 q = 0) : d380371 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380328, d380371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39898 q selected
    | true =>
      simp only [d380328, d380371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380329 q = 0) : d380372 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380329, d380372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380329, d380372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380330 q = 0) : d380373 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380330, d380373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380330, d380373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380331 q = 0) : d380374 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380331, d380374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380331, d380374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380332 q = 0) : d380375 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380332, d380375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380332, d380375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39900 (p : Pattern) (selected : d380338 p = 0) : d380381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380333 q = 0) : d380376 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380333, d380376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39899 q selected
    | true =>
      simp only [d380333, d380376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380334 q = 0) : d380377 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380334, d380377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380334, d380377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380335 q = 0) : d380378 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380335, d380378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380335, d380378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380336 q = 0) : d380379 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380336, d380379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380336, d380379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380337 q = 0) : d380380 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380337, d380380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380337, d380380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380338 q = 0) : d380381 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380338, d380381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380338, d380381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39901 (p : Pattern) (selected : d380344 p = 0) : d380387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380339 q = 0) : d380382 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380339, d380382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39900 q selected
    | true =>
      simp only [d380339, d380382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380340 q = 0) : d380383 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380340, d380383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380340, d380383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380341 q = 0) : d380384 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380341, d380384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380341, d380384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380342 q = 0) : d380385 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380342, d380385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380342, d380385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380343 q = 0) : d380386 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380343, d380386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380343, d380386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380344 q = 0) : d380387 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380344, d380387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380344, d380387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39902 (p : Pattern) (selected : d380350 p = 0) : d380393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380345 q = 0) : d380388 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380345, d380388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39901 q selected
    | true =>
      simp only [d380345, d380388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380346 q = 0) : d380389 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380346, d380389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380346, d380389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380347 q = 0) : d380390 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380347, d380390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380347, d380390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380348 q = 0) : d380391 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380348, d380391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380348, d380391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380349 q = 0) : d380392 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380349, d380392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380349, d380392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380350 q = 0) : d380393 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380350, d380393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380350, d380393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39903 (p : Pattern) (selected : d380356 p = 0) : d380399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380351 q = 0) : d380394 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380351, d380394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39902 q selected
    | true =>
      simp only [d380351, d380394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380352 q = 0) : d380395 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380352, d380395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380352, d380395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380353 q = 0) : d380396 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380353, d380396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380353, d380396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380354 q = 0) : d380397 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380354, d380397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380354, d380397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380355 q = 0) : d380398 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380355, d380398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380355, d380398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380356 q = 0) : d380399 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380356, d380399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380356, d380399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39904 (p : Pattern) (selected : d380362 p = 0) : d380405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380357 q = 0) : d380400 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380357, d380400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39903 q selected
    | true =>
      simp only [d380357, d380400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380358 q = 0) : d380401 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380358, d380401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380358, d380401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380359 q = 0) : d380402 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380359, d380402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380359, d380402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380360 q = 0) : d380403 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380360, d380403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380360, d380403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380361 q = 0) : d380404 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380361, d380404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380361, d380404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380362 q = 0) : d380405 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380362, d380405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380362, d380405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39905 (p : Pattern) (selected : d380321 p = 1) : d380407 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d45903 q = 1) : d322162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d45903, d322162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33501 q selected
  have h3 (q : Pattern) (selected : d45904 q = 1) : d322163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d45904, d322163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d47372 q = 1) : d379324 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47372, d379324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47372, d379324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d380320 q = 1) : d380406 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380320, d380406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380320, d380406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d380321 q = 1) : d380407 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380321, d380407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380321, d380407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro39906 (p : Pattern) (selected : d380327 p = 1) : d380413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380322 q = 1) : d380408 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380322, d380408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39905 q selected
    | true =>
      simp only [d380322, d380408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380323 q = 1) : d380409 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380323, d380409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380323, d380409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380324 q = 1) : d380410 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380324, d380410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380324, d380410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380325 q = 1) : d380411 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380325, d380411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380325, d380411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380326 q = 1) : d380412 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380326, d380412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380326, d380412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380327 q = 1) : d380413 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380327, d380413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380327, d380413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39907 (p : Pattern) (selected : d380332 p = 1) : d380418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380328 q = 1) : d380414 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380328, d380414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39906 q selected
    | true =>
      simp only [d380328, d380414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380329 q = 1) : d380415 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380329, d380415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380329, d380415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380330 q = 1) : d380416 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380330, d380416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380330, d380416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380331 q = 1) : d380417 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380331, d380417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380331, d380417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380332 q = 1) : d380418 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380332, d380418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380332, d380418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39908 (p : Pattern) (selected : d380338 p = 1) : d380424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380333 q = 1) : d380419 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380333, d380419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39907 q selected
    | true =>
      simp only [d380333, d380419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380334 q = 1) : d380420 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380334, d380420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380334, d380420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380335 q = 1) : d380421 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380335, d380421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380335, d380421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380336 q = 1) : d380422 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380336, d380422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380336, d380422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380337 q = 1) : d380423 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380337, d380423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380337, d380423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380338 q = 1) : d380424 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380338, d380424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380338, d380424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39909 (p : Pattern) (selected : d380344 p = 1) : d380430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380339 q = 1) : d380425 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380339, d380425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39908 q selected
    | true =>
      simp only [d380339, d380425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380340 q = 1) : d380426 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380340, d380426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380340, d380426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380341 q = 1) : d380427 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380341, d380427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380341, d380427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380342 q = 1) : d380428 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380342, d380428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380342, d380428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380343 q = 1) : d380429 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380343, d380429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380343, d380429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380344 q = 1) : d380430 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380344, d380430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380344, d380430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39910 (p : Pattern) (selected : d380350 p = 1) : d380436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380345 q = 1) : d380431 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380345, d380431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39909 q selected
    | true =>
      simp only [d380345, d380431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380346 q = 1) : d380432 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380346, d380432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380346, d380432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380347 q = 1) : d380433 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380347, d380433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380347, d380433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380348 q = 1) : d380434 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380348, d380434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380348, d380434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380349 q = 1) : d380435 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380349, d380435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380349, d380435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380350 q = 1) : d380436 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380350, d380436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380350, d380436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39911 (p : Pattern) (selected : d380356 p = 1) : d380442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380351 q = 1) : d380437 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380351, d380437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39910 q selected
    | true =>
      simp only [d380351, d380437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380352 q = 1) : d380438 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380352, d380438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380352, d380438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380353 q = 1) : d380439 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380353, d380439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380353, d380439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380354 q = 1) : d380440 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380354, d380440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380354, d380440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380355 q = 1) : d380441 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380355, d380441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380355, d380441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380356 q = 1) : d380442 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380356, d380442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380356, d380442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39912 (p : Pattern) (selected : d380362 p = 1) : d380448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380357 q = 1) : d380443 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380357, d380443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39911 q selected
    | true =>
      simp only [d380357, d380443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380358 q = 1) : d380444 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380358, d380444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380358, d380444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380359 q = 1) : d380445 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380359, d380445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380359, d380445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380360 q = 1) : d380446 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380360, d380446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380360, d380446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380361 q = 1) : d380447 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380361, d380447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380361, d380447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380362 q = 1) : d380448 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380362, d380448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380362, d380448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39913 (p : Pattern) (selected : d47513 p = 0) : d380455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44964 q = 0) : d318809 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d318809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44964, d318809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33010 q selected
  have h6 (q : Pattern) (selected : d44965 q = 0) : d318810 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d318810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44965, d318810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44966 q = 0) : d318811 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d318811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44966, d318811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44967 q = 0) : d318812 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d318812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44967, d318812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44968 q = 0) : d318813 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d318813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44968, d318813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47513 q = 0) : d380455 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47513, d380455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47513, d380455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39914 (p : Pattern) (selected : d47519 p = 0) : d380461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47514 q = 0) : d380456 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47514, d380456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39913 q selected
    | true =>
      simp only [d47514, d380456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47515 q = 0) : d380457 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47515, d380457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47515, d380457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47516 q = 0) : d380458 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47516, d380458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47516, d380458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47517 q = 0) : d380459 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47517, d380459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47517, d380459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47518 q = 0) : d380460 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47518, d380460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47518, d380460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47519 q = 0) : d380461 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47519, d380461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47519, d380461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39915 (p : Pattern) (selected : d47525 p = 0) : d380467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47520 q = 0) : d380462 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47520, d380462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39914 q selected
    | true =>
      simp only [d47520, d380462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47521 q = 0) : d380463 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47521, d380463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47521, d380463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47522 q = 0) : d380464 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47522, d380464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47522, d380464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47523 q = 0) : d380465 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47523, d380465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47523, d380465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47524 q = 0) : d380466 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47524, d380466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47524, d380466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47525 q = 0) : d380467 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47525, d380467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47525, d380467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39916 (p : Pattern) (selected : d47531 p = 0) : d380473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47526 q = 0) : d380468 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47526, d380468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39915 q selected
    | true =>
      simp only [d47526, d380468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47527 q = 0) : d380469 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47527, d380469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47527, d380469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47528 q = 0) : d380470 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47528, d380470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47528, d380470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47529 q = 0) : d380471 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47529, d380471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47529, d380471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47530 q = 0) : d380472 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47530, d380472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47530, d380472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47531 q = 0) : d380473 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47531, d380473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47531, d380473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39917 (p : Pattern) (selected : d47537 p = 0) : d380479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47532 q = 0) : d380474 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47532, d380474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39916 q selected
    | true =>
      simp only [d47532, d380474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47533 q = 0) : d380475 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47533, d380475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47533, d380475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47534 q = 0) : d380476 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47534, d380476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47534, d380476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47535 q = 0) : d380477 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47535, d380477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47535, d380477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47536 q = 0) : d380478 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47536, d380478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47536, d380478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47537 q = 0) : d380479 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47537, d380479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47537, d380479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39918 (p : Pattern) (selected : d47543 p = 0) : d380485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47538 q = 0) : d380480 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47538, d380480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39917 q selected
    | true =>
      simp only [d47538, d380480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47539 q = 0) : d380481 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47539, d380481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47539, d380481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47540 q = 0) : d380482 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47540, d380482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47540, d380482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47541 q = 0) : d380483 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47541, d380483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47541, d380483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47542 q = 0) : d380484 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47542, d380484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47542, d380484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47543 q = 0) : d380485 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47543, d380485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47543, d380485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39919 (p : Pattern) (selected : d47549 p = 0) : d380491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47544 q = 0) : d380486 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47544, d380486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39918 q selected
    | true =>
      simp only [d47544, d380486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47545 q = 0) : d380487 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47545, d380487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47545, d380487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47546 q = 0) : d380488 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47546, d380488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47546, d380488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47547 q = 0) : d380489 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47547, d380489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47547, d380489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47548 q = 0) : d380490 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47548, d380490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47548, d380490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47549 q = 0) : d380491 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47549, d380491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47549, d380491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39920 (p : Pattern) (selected : d47555 p = 0) : d380497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47550 q = 0) : d380492 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47550, d380492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39919 q selected
    | true =>
      simp only [d47550, d380492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47551 q = 0) : d380493 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47551, d380493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47551, d380493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47552 q = 0) : d380494 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47552, d380494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47552, d380494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47553 q = 0) : d380495 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47553, d380495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47553, d380495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47554 q = 0) : d380496 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47554, d380496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47554, d380496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47555 q = 0) : d380497 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47555, d380497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47555, d380497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39921 (p : Pattern) (selected : d47561 p = 0) : d380503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47556 q = 0) : d380498 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47556, d380498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39920 q selected
    | true =>
      simp only [d47556, d380498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47557 q = 0) : d380499 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47557, d380499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47557, d380499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47558 q = 0) : d380500 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47558, d380500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47558, d380500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47559 q = 0) : d380501 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47559, d380501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47559, d380501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47560 q = 0) : d380502 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47560, d380502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47560, d380502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47561 q = 0) : d380503 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47561, d380503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47561, d380503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39922 (p : Pattern) (selected : d47470 p = 2) : d380116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47465 q = 2) : d380111 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47465, d380111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38288 q selected
    | true =>
      simp only [d47465, d380111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47466 q = 2) : d380112 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47466, d380112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47466, d380112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47467 q = 2) : d380113 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47467, d380113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47467, d380113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47468 q = 2) : d380114 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47468, d380114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47468, d380114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47469 q = 2) : d380115 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47469, d380115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47469, d380115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47470 q = 2) : d380116 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47470, d380116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47470, d380116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39923 (p : Pattern) (selected : d47476 p = 2) : d380122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47471 q = 2) : d380117 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47471, d380117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39922 q selected
    | true =>
      simp only [d47471, d380117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47472 q = 2) : d380118 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47472, d380118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47472, d380118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47473 q = 2) : d380119 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47473, d380119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47473, d380119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47474 q = 2) : d380120 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47474, d380120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47474, d380120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47475 q = 2) : d380121 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47475, d380121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47475, d380121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47476 q = 2) : d380122 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47476, d380122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47476, d380122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39924 (p : Pattern) (selected : d47482 p = 2) : d380128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47477 q = 2) : d380123 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47477, d380123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39923 q selected
    | true =>
      simp only [d47477, d380123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47478 q = 2) : d380124 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47478, d380124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47478, d380124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47479 q = 2) : d380125 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47479, d380125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47479, d380125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47480 q = 2) : d380126 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47480, d380126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47480, d380126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47481 q = 2) : d380127 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47481, d380127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47481, d380127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47482 q = 2) : d380128 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47482, d380128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47482, d380128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39925 (p : Pattern) (selected : d47488 p = 2) : d380134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47483 q = 2) : d380129 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47483, d380129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39924 q selected
    | true =>
      simp only [d47483, d380129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47484 q = 2) : d380130 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47484, d380130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47484, d380130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47485 q = 2) : d380131 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47485, d380131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47485, d380131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47486 q = 2) : d380132 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47486, d380132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47486, d380132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47487 q = 2) : d380133 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47487, d380133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47487, d380133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47488 q = 2) : d380134 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47488, d380134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47488, d380134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39926 (p : Pattern) (selected : d47494 p = 2) : d380140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47489 q = 2) : d380135 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47489, d380135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39925 q selected
    | true =>
      simp only [d47489, d380135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47490 q = 2) : d380136 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47490, d380136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47490, d380136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47491 q = 2) : d380137 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47491, d380137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47491, d380137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47492 q = 2) : d380138 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47492, d380138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47492, d380138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47493 q = 2) : d380139 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47493, d380139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47493, d380139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47494 q = 2) : d380140 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47494, d380140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47494, d380140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39927 (p : Pattern) (selected : d47500 p = 2) : d380146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47495 q = 2) : d380141 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47495, d380141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39926 q selected
    | true =>
      simp only [d47495, d380141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47496 q = 2) : d380142 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47496, d380142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47496, d380142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47497 q = 2) : d380143 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47497, d380143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47497, d380143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47498 q = 2) : d380144 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47498, d380144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47498, d380144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47499 q = 2) : d380145 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47499, d380145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47499, d380145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47500 q = 2) : d380146 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47500, d380146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47500, d380146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39928 (p : Pattern) (selected : d47506 p = 2) : d380152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47501 q = 2) : d380147 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47501, d380147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39927 q selected
    | true =>
      simp only [d47501, d380147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47502 q = 2) : d380148 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47502, d380148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47502, d380148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47503 q = 2) : d380149 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47503, d380149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47503, d380149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47504 q = 2) : d380150 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47504, d380150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47504, d380150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47505 q = 2) : d380151 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47505, d380151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47505, d380151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47506 q = 2) : d380152 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47506, d380152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47506, d380152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39929 (p : Pattern) (selected : d47512 p = 2) : d380158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47507 q = 2) : d380153 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47507, d380153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39928 q selected
    | true =>
      simp only [d47507, d380153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47508 q = 2) : d380154 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47508, d380154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47508, d380154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47509 q = 2) : d380155 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47509, d380155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47509, d380155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47510 q = 2) : d380156 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47510, d380156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47510, d380156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47511 q = 2) : d380157 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47511, d380157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47511, d380157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47512 q = 2) : d380158 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47512, d380158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47512, d380158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39930 (p : Pattern) (selected : d47513 p = 1) : d380504 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d44964 q = 1) : d322039 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44964, d322039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33437 q selected
  have h3 (q : Pattern) (selected : d44965 q = 1) : d322040 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44965, d322040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44966 q = 1) : d322041 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44966, d322041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44967 q = 1) : d322042 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44967, d322042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44968 q = 1) : d322043 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44968, d322043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d47513 q = 1) : d380504 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47513, d380504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d47513, d380504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro39931 (p : Pattern) (selected : d47519 p = 1) : d380510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47514 q = 1) : d380505 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47514, d380505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39930 q selected
    | true =>
      simp only [d47514, d380505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47515 q = 1) : d380506 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47515, d380506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47515, d380506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47516 q = 1) : d380507 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47516, d380507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47516, d380507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47517 q = 1) : d380508 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47517, d380508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47517, d380508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47518 q = 1) : d380509 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47518, d380509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47518, d380509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47519 q = 1) : d380510 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47519, d380510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47519, d380510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39932 (p : Pattern) (selected : d47525 p = 1) : d380516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47520 q = 1) : d380511 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47520, d380511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39931 q selected
    | true =>
      simp only [d47520, d380511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47521 q = 1) : d380512 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47521, d380512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47521, d380512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47522 q = 1) : d380513 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47522, d380513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47522, d380513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47523 q = 1) : d380514 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47523, d380514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47523, d380514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47524 q = 1) : d380515 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47524, d380515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47524, d380515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47525 q = 1) : d380516 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47525, d380516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47525, d380516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39933 (p : Pattern) (selected : d47531 p = 1) : d380522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47526 q = 1) : d380517 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47526, d380517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39932 q selected
    | true =>
      simp only [d47526, d380517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47527 q = 1) : d380518 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47527, d380518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47527, d380518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47528 q = 1) : d380519 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47528, d380519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47528, d380519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47529 q = 1) : d380520 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47529, d380520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47529, d380520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47530 q = 1) : d380521 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47530, d380521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47530, d380521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47531 q = 1) : d380522 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47531, d380522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47531, d380522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39934 (p : Pattern) (selected : d47537 p = 1) : d380528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47532 q = 1) : d380523 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47532, d380523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39933 q selected
    | true =>
      simp only [d47532, d380523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47533 q = 1) : d380524 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47533, d380524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47533, d380524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47534 q = 1) : d380525 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47534, d380525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47534, d380525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47535 q = 1) : d380526 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47535, d380526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47535, d380526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47536 q = 1) : d380527 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47536, d380527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47536, d380527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47537 q = 1) : d380528 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47537, d380528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47537, d380528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39935 (p : Pattern) (selected : d47543 p = 1) : d380534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47538 q = 1) : d380529 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47538, d380529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39934 q selected
    | true =>
      simp only [d47538, d380529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47539 q = 1) : d380530 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47539, d380530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47539, d380530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47540 q = 1) : d380531 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47540, d380531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47540, d380531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47541 q = 1) : d380532 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47541, d380532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47541, d380532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47542 q = 1) : d380533 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47542, d380533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47542, d380533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47543 q = 1) : d380534 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47543, d380534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47543, d380534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39936 (p : Pattern) (selected : d47549 p = 1) : d380540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47544 q = 1) : d380535 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47544, d380535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39935 q selected
    | true =>
      simp only [d47544, d380535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47545 q = 1) : d380536 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47545, d380536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47545, d380536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47546 q = 1) : d380537 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47546, d380537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47546, d380537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47547 q = 1) : d380538 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47547, d380538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47547, d380538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47548 q = 1) : d380539 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47548, d380539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47548, d380539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47549 q = 1) : d380540 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47549, d380540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47549, d380540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39937 (p : Pattern) (selected : d47555 p = 1) : d380546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47550 q = 1) : d380541 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47550, d380541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39936 q selected
    | true =>
      simp only [d47550, d380541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47551 q = 1) : d380542 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47551, d380542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47551, d380542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47552 q = 1) : d380543 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47552, d380543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47552, d380543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47553 q = 1) : d380544 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47553, d380544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47553, d380544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47554 q = 1) : d380545 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47554, d380545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47554, d380545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47555 q = 1) : d380546 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47555, d380546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47555, d380546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39938 (p : Pattern) (selected : d47561 p = 1) : d380552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47556 q = 1) : d380547 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47556, d380547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39937 q selected
    | true =>
      simp only [d47556, d380547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47557 q = 1) : d380548 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47557, d380548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47557, d380548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47558 q = 1) : d380549 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47558, d380549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47558, d380549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47559 q = 1) : d380550 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47559, d380550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47559, d380550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47560 q = 1) : d380551 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47560, d380551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47560, d380551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47561 q = 1) : d380552 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47561, d380552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47561, d380552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39939 (p : Pattern) (selected : d380611 p = 0) : d380659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d380611 q = 0) : d380659 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380611, d380659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380611, d380659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39940 (p : Pattern) (selected : d380617 p = 0) : d380665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380612 q = 0) : d380660 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380612, d380660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39939 q selected
    | true =>
      simp only [d380612, d380660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380613 q = 0) : d380661 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380613, d380661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380613, d380661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380614 q = 0) : d380662 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380614, d380662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380614, d380662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380615 q = 0) : d380663 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380615, d380663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380615, d380663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380616 q = 0) : d380664 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380616, d380664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380616, d380664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380617 q = 0) : d380665 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380617, d380665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380617, d380665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39941 (p : Pattern) (selected : d380622 p = 0) : d380670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380618 q = 0) : d380666 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380618, d380666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39940 q selected
    | true =>
      simp only [d380618, d380666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380619 q = 0) : d380667 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380619, d380667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380619, d380667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380620 q = 0) : d380668 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380620, d380668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380620, d380668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380621 q = 0) : d380669 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380621, d380669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380621, d380669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380622 q = 0) : d380670 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380622, d380670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380622, d380670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39942 (p : Pattern) (selected : d380628 p = 0) : d380676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380623 q = 0) : d380671 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380623, d380671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39941 q selected
    | true =>
      simp only [d380623, d380671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380624 q = 0) : d380672 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380624, d380672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380624, d380672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380625 q = 0) : d380673 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380625, d380673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380625, d380673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380626 q = 0) : d380674 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380626, d380674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380626, d380674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380627 q = 0) : d380675 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380627, d380675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380627, d380675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380628 q = 0) : d380676 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380628, d380676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380628, d380676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39943 (p : Pattern) (selected : d380634 p = 0) : d380682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380629 q = 0) : d380677 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380629, d380677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39942 q selected
    | true =>
      simp only [d380629, d380677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380630 q = 0) : d380678 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380630, d380678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380630, d380678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380631 q = 0) : d380679 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380631, d380679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380631, d380679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380632 q = 0) : d380680 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380632, d380680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380632, d380680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380633 q = 0) : d380681 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380633, d380681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380633, d380681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380634 q = 0) : d380682 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380634, d380682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380634, d380682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39944 (p : Pattern) (selected : d380640 p = 0) : d380688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380635 q = 0) : d380683 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380635, d380683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39943 q selected
    | true =>
      simp only [d380635, d380683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380636 q = 0) : d380684 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380636, d380684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380636, d380684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380637 q = 0) : d380685 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380637, d380685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380637, d380685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380638 q = 0) : d380686 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380638, d380686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380638, d380686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380639 q = 0) : d380687 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380639, d380687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380639, d380687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380640 q = 0) : d380688 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380640, d380688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380640, d380688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39945 (p : Pattern) (selected : d380646 p = 0) : d380694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380641 q = 0) : d380689 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380641, d380689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39944 q selected
    | true =>
      simp only [d380641, d380689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380642 q = 0) : d380690 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380642, d380690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380642, d380690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380643 q = 0) : d380691 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380643, d380691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380643, d380691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380644 q = 0) : d380692 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380644, d380692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380644, d380692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380645 q = 0) : d380693 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380645, d380693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380645, d380693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380646 q = 0) : d380694 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380646, d380694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380646, d380694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39946 (p : Pattern) (selected : d380652 p = 0) : d380700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380647 q = 0) : d380695 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380647, d380695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39945 q selected
    | true =>
      simp only [d380647, d380695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380648 q = 0) : d380696 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380648, d380696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380648, d380696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380649 q = 0) : d380697 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380649, d380697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380649, d380697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380650 q = 0) : d380698 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380650, d380698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380650, d380698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380651 q = 0) : d380699 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380651, d380699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380651, d380699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380652 q = 0) : d380700 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380652, d380700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380652, d380700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39947 (p : Pattern) (selected : d380658 p = 0) : d380706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380653 q = 0) : d380701 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380653, d380701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39946 q selected
    | true =>
      simp only [d380653, d380701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380654 q = 0) : d380702 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380654, d380702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380654, d380702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380655 q = 0) : d380703 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380655, d380703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380655, d380703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380656 q = 0) : d380704 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380656, d380704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380656, d380704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380657 q = 0) : d380705 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380657, d380705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380657, d380705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380658 q = 0) : d380706 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380658, d380706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380658, d380706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39948 (p : Pattern) (selected : d380658 p = 1) : d380658 p = 1 := by
  have h0 (q : Pattern) (selected : d380658 q = 1) : d380658 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro39949 (p : Pattern) (selected : d380720 p = 0) : d380764 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 0) : d319211 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d45496, d319211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33107 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d47418 q = 0) : d379584 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47418, d379584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47418, d379584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d380718 q = 0) : d380762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380718, d380762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380718, d380762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d380719 q = 0) : d380763 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380719, d380763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380719, d380763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d380720 q = 0) : d380764 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380720, d380764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380720, d380764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro39950 (p : Pattern) (selected : d380726 p = 0) : d380770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380721 q = 0) : d380765 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380721, d380765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39949 q selected
    | true =>
      simp only [d380721, d380765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380722 q = 0) : d380766 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380722, d380766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380722, d380766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380723 q = 0) : d380767 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380723, d380767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380723, d380767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380724 q = 0) : d380768 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380724, d380768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380724, d380768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380725 q = 0) : d380769 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380725, d380769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380725, d380769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380726 q = 0) : d380770 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380726, d380770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380726, d380770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39951 (p : Pattern) (selected : d380731 p = 0) : d380775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380727 q = 0) : d380771 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380727, d380771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39950 q selected
    | true =>
      simp only [d380727, d380771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380728 q = 0) : d380772 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380728, d380772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380728, d380772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380729 q = 0) : d380773 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380729, d380773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380729, d380773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380730 q = 0) : d380774 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380730, d380774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380730, d380774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380731 q = 0) : d380775 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380731, d380775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380731, d380775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39952 (p : Pattern) (selected : d380737 p = 0) : d380781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380732 q = 0) : d380776 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380732, d380776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39951 q selected
    | true =>
      simp only [d380732, d380776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380733 q = 0) : d380777 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380733, d380777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380733, d380777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380734 q = 0) : d380778 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380734, d380778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380734, d380778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380735 q = 0) : d380779 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380735, d380779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380735, d380779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380736 q = 0) : d380780 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380736, d380780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380736, d380780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380737 q = 0) : d380781 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380737, d380781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380737, d380781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39953 (p : Pattern) (selected : d380743 p = 0) : d380787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380738 q = 0) : d380782 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380738, d380782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39952 q selected
    | true =>
      simp only [d380738, d380782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380739 q = 0) : d380783 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380739, d380783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380739, d380783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380740 q = 0) : d380784 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380740, d380784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380740, d380784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380741 q = 0) : d380785 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380741, d380785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380741, d380785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380742 q = 0) : d380786 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380742, d380786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380742, d380786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380743 q = 0) : d380787 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380743, d380787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380743, d380787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39954 (p : Pattern) (selected : d380749 p = 0) : d380793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380744 q = 0) : d380788 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380744, d380788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39953 q selected
    | true =>
      simp only [d380744, d380788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380745 q = 0) : d380789 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380745, d380789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380745, d380789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380746 q = 0) : d380790 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380746, d380790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380746, d380790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380747 q = 0) : d380791 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380747, d380791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380747, d380791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380748 q = 0) : d380792 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380748, d380792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380748, d380792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380749 q = 0) : d380793 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380749, d380793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380749, d380793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39955 (p : Pattern) (selected : d380755 p = 0) : d380799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380750 q = 0) : d380794 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380750, d380794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39954 q selected
    | true =>
      simp only [d380750, d380794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380751 q = 0) : d380795 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380751, d380795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380751, d380795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380752 q = 0) : d380796 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380752, d380796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380752, d380796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380753 q = 0) : d380797 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380753, d380797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380753, d380797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380754 q = 0) : d380798 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380754, d380798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380754, d380798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380755 q = 0) : d380799 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380755, d380799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380755, d380799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39956 (p : Pattern) (selected : d380761 p = 0) : d380805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380756 q = 0) : d380800 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380756, d380800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39955 q selected
    | true =>
      simp only [d380756, d380800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380757 q = 0) : d380801 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380757, d380801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380757, d380801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380758 q = 0) : d380802 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380758, d380802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380758, d380802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380759 q = 0) : d380803 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380759, d380803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380759, d380803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380760 q = 0) : d380804 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380760, d380804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380760, d380804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380761 q = 0) : d380805 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380761, d380805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380761, d380805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39957 (p : Pattern) (selected : d380720 p = 1) : d380808 p = 1 := by
  have h0 (q : Pattern) (selected : d45496 q = 1) : d322122 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d45496, d322122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33473 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d47418 q = 1) : d379631 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47418, d379631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47418, d379631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d380718 q = 1) : d380806 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380718, d380806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380718, d380806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d380719 q = 1) : d380807 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380719, d380807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380719, d380807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d380720 q = 1) : d380808 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380720, d380808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380720, d380808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro39958 (p : Pattern) (selected : d380726 p = 1) : d380814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380721 q = 1) : d380809 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380721, d380809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39957 q selected
    | true =>
      simp only [d380721, d380809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380722 q = 1) : d380810 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380722, d380810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380722, d380810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380723 q = 1) : d380811 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380723, d380811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380723, d380811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380724 q = 1) : d380812 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380724, d380812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380724, d380812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380725 q = 1) : d380813 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380725, d380813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380725, d380813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380726 q = 1) : d380814 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380726, d380814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380726, d380814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39959 (p : Pattern) (selected : d380731 p = 1) : d380819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380727 q = 1) : d380815 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380727, d380815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39958 q selected
    | true =>
      simp only [d380727, d380815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380728 q = 1) : d380816 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380728, d380816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380728, d380816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380729 q = 1) : d380817 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380729, d380817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380729, d380817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380730 q = 1) : d380818 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380730, d380818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380730, d380818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380731 q = 1) : d380819 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380731, d380819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380731, d380819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39960 (p : Pattern) (selected : d380737 p = 1) : d380825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380732 q = 1) : d380820 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380732, d380820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39959 q selected
    | true =>
      simp only [d380732, d380820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380733 q = 1) : d380821 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380733, d380821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380733, d380821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380734 q = 1) : d380822 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380734, d380822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380734, d380822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380735 q = 1) : d380823 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380735, d380823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380735, d380823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380736 q = 1) : d380824 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380736, d380824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380736, d380824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380737 q = 1) : d380825 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380737, d380825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380737, d380825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39961 (p : Pattern) (selected : d380743 p = 1) : d380831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380738 q = 1) : d380826 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380738, d380826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39960 q selected
    | true =>
      simp only [d380738, d380826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380739 q = 1) : d380827 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380739, d380827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380739, d380827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380740 q = 1) : d380828 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380740, d380828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380740, d380828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380741 q = 1) : d380829 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380741, d380829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380741, d380829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380742 q = 1) : d380830 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380742, d380830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380742, d380830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380743 q = 1) : d380831 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380743, d380831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380743, d380831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39962 (p : Pattern) (selected : d380749 p = 1) : d380837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380744 q = 1) : d380832 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380744, d380832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39961 q selected
    | true =>
      simp only [d380744, d380832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380745 q = 1) : d380833 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380745, d380833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380745, d380833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380746 q = 1) : d380834 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380746, d380834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380746, d380834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380747 q = 1) : d380835 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380747, d380835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380747, d380835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380748 q = 1) : d380836 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380748, d380836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380748, d380836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380749 q = 1) : d380837 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380749, d380837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380749, d380837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39963 (p : Pattern) (selected : d380755 p = 1) : d380843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380750 q = 1) : d380838 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380750, d380838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39962 q selected
    | true =>
      simp only [d380750, d380838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380751 q = 1) : d380839 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380751, d380839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380751, d380839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380752 q = 1) : d380840 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380752, d380840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380752, d380840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380753 q = 1) : d380841 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380753, d380841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380753, d380841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380754 q = 1) : d380842 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380754, d380842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380754, d380842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380755 q = 1) : d380843 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380755, d380843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380755, d380843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39964 (p : Pattern) (selected : d380761 p = 1) : d380849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380756 q = 1) : d380844 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380756, d380844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39963 q selected
    | true =>
      simp only [d380756, d380844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380757 q = 1) : d380845 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380757, d380845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380757, d380845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380758 q = 1) : d380846 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380758, d380846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380758, d380846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380759 q = 1) : d380847 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380759, d380847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380759, d380847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380760 q = 1) : d380848 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380760, d380848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380760, d380848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380761 q = 1) : d380849 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380761, d380849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380761, d380849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39965 (p : Pattern) (selected : d47563 p = 0) : d380857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47562 q = 0) : d380856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47563 q = 0) : d380857 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47563, d380857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47563, d380857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39966 (p : Pattern) (selected : d47569 p = 0) : d380863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47564 q = 0) : d380858 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47564, d380858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39965 q selected
    | true =>
      simp only [d47564, d380858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47565 q = 0) : d380859 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47565, d380859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47565, d380859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47566 q = 0) : d380860 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47566, d380860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47566, d380860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47567 q = 0) : d380861 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47567, d380861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47567, d380861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47568 q = 0) : d380862 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47568, d380862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47568, d380862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47569 q = 0) : d380863 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47569, d380863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47569, d380863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39967 (p : Pattern) (selected : d47575 p = 0) : d380869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47570 q = 0) : d380864 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47570, d380864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39966 q selected
    | true =>
      simp only [d47570, d380864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47571 q = 0) : d380865 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47571, d380865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47571, d380865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47572 q = 0) : d380866 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, d380866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47572, d380866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47573 q = 0) : d380867 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, d380867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47573, d380867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47574 q = 0) : d380868 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, d380868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47574, d380868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47575 q = 0) : d380869 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, d380869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47575, d380869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39968 (p : Pattern) (selected : d47581 p = 0) : d380875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47576 q = 0) : d380870 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, d380870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39967 q selected
    | true =>
      simp only [d47576, d380870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47577 q = 0) : d380871 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, d380871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47577, d380871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47578 q = 0) : d380872 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, d380872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47578, d380872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47579 q = 0) : d380873 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, d380873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47579, d380873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47580 q = 0) : d380874 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, d380874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47580, d380874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47581 q = 0) : d380875 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, d380875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47581, d380875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39969 (p : Pattern) (selected : d47587 p = 0) : d380881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47582 q = 0) : d380876 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, d380876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39968 q selected
    | true =>
      simp only [d47582, d380876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47583 q = 0) : d380877 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, d380877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47583, d380877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47584 q = 0) : d380878 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, d380878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47584, d380878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47585 q = 0) : d380879 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, d380879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47585, d380879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47586 q = 0) : d380880 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, d380880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47586, d380880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47587 q = 0) : d380881 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, d380881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47587, d380881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39970 (p : Pattern) (selected : d47593 p = 0) : d380887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47588 q = 0) : d380882 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, d380882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39969 q selected
    | true =>
      simp only [d47588, d380882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47589 q = 0) : d380883 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, d380883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47589, d380883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47590 q = 0) : d380884 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, d380884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47590, d380884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47591 q = 0) : d380885 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, d380885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47591, d380885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47592 q = 0) : d380886 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, d380886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47592, d380886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47593 q = 0) : d380887 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, d380887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47593, d380887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39971 (p : Pattern) (selected : d47599 p = 0) : d380893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47594 q = 0) : d380888 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, d380888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39970 q selected
    | true =>
      simp only [d47594, d380888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47595 q = 0) : d380889 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, d380889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47595, d380889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47596 q = 0) : d380890 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, d380890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47596, d380890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47597 q = 0) : d380891 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, d380891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47597, d380891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47598 q = 0) : d380892 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, d380892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47598, d380892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47599 q = 0) : d380893 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, d380893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47599, d380893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39972 (p : Pattern) (selected : d47605 p = 0) : d380899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47600 q = 0) : d380894 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, d380894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39971 q selected
    | true =>
      simp only [d47600, d380894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47601 q = 0) : d380895 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, d380895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47601, d380895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47602 q = 0) : d380896 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, d380896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47602, d380896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47603 q = 0) : d380897 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, d380897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47603, d380897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47604 q = 0) : d380898 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, d380898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47604, d380898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47605 q = 0) : d380899 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, d380899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47605, d380899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39973 (p : Pattern) (selected : d47611 p = 0) : d380905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47606 q = 0) : d380900 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, d380900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39972 q selected
    | true =>
      simp only [d47606, d380900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47607 q = 0) : d380901 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, d380901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47607, d380901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47608 q = 0) : d380902 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, d380902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47608, d380902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47609 q = 0) : d380903 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, d380903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47609, d380903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47610 q = 0) : d380904 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, d380904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47610, d380904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47611 q = 0) : d380905 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, d380905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47611, d380905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39974 (p : Pattern) (selected : d47513 p = 2) : d380553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d96 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro657 q selected
  have h2 (q : Pattern) (selected : d97 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44964 q = 2) : d53648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44964, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44964, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38253 q selected
  have h6 (q : Pattern) (selected : d44965 q = 2) : d53649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44965, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44965, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44966 q = 2) : d53650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44966, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44966, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44967 q = 2) : d53651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44967, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44967, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44968 q = 2) : d53652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44968, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44968, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d47513 q = 2) : d380553 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47513, d380553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d47513, d380553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro39975 (p : Pattern) (selected : d47519 p = 2) : d380559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47514 q = 2) : d380554 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47514, d380554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39974 q selected
    | true =>
      simp only [d47514, d380554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47515 q = 2) : d380555 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47515, d380555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47515, d380555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47516 q = 2) : d380556 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47516, d380556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47516, d380556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47517 q = 2) : d380557 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47517, d380557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47517, d380557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47518 q = 2) : d380558 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47518, d380558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47518, d380558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47519 q = 2) : d380559 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47519, d380559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47519, d380559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39976 (p : Pattern) (selected : d47525 p = 2) : d380565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47520 q = 2) : d380560 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47520, d380560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39975 q selected
    | true =>
      simp only [d47520, d380560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47521 q = 2) : d380561 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47521, d380561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47521, d380561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47522 q = 2) : d380562 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47522, d380562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47522, d380562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47523 q = 2) : d380563 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47523, d380563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47523, d380563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47524 q = 2) : d380564 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47524, d380564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47524, d380564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47525 q = 2) : d380565 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47525, d380565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47525, d380565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39977 (p : Pattern) (selected : d47531 p = 2) : d380571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47526 q = 2) : d380566 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47526, d380566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39976 q selected
    | true =>
      simp only [d47526, d380566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47527 q = 2) : d380567 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47527, d380567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47527, d380567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47528 q = 2) : d380568 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47528, d380568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47528, d380568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47529 q = 2) : d380569 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47529, d380569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47529, d380569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47530 q = 2) : d380570 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47530, d380570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47530, d380570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47531 q = 2) : d380571 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47531, d380571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47531, d380571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39978 (p : Pattern) (selected : d47537 p = 2) : d380577 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47532 q = 2) : d380572 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47532, d380572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39977 q selected
    | true =>
      simp only [d47532, d380572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47533 q = 2) : d380573 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47533, d380573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47533, d380573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47534 q = 2) : d380574 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47534, d380574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47534, d380574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47535 q = 2) : d380575 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47535, d380575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47535, d380575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47536 q = 2) : d380576 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47536, d380576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47536, d380576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47537 q = 2) : d380577 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47537, d380577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47537, d380577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39979 (p : Pattern) (selected : d47543 p = 2) : d380583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47538 q = 2) : d380578 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47538, d380578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39978 q selected
    | true =>
      simp only [d47538, d380578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47539 q = 2) : d380579 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47539, d380579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47539, d380579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47540 q = 2) : d380580 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47540, d380580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47540, d380580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47541 q = 2) : d380581 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47541, d380581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47541, d380581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47542 q = 2) : d380582 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47542, d380582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47542, d380582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47543 q = 2) : d380583 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47543, d380583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47543, d380583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39980 (p : Pattern) (selected : d47549 p = 2) : d380589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47544 q = 2) : d380584 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47544, d380584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39979 q selected
    | true =>
      simp only [d47544, d380584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47545 q = 2) : d380585 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47545, d380585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47545, d380585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47546 q = 2) : d380586 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47546, d380586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47546, d380586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47547 q = 2) : d380587 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47547, d380587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47547, d380587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47548 q = 2) : d380588 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47548, d380588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47548, d380588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47549 q = 2) : d380589 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47549, d380589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47549, d380589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39981 (p : Pattern) (selected : d47555 p = 2) : d380595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47550 q = 2) : d380590 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47550, d380590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39980 q selected
    | true =>
      simp only [d47550, d380590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47551 q = 2) : d380591 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47551, d380591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47551, d380591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47552 q = 2) : d380592 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47552, d380592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47552, d380592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47553 q = 2) : d380593 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47553, d380593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47553, d380593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47554 q = 2) : d380594 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47554, d380594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47554, d380594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47555 q = 2) : d380595 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47555, d380595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47555, d380595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39982 (p : Pattern) (selected : d47561 p = 2) : d380601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47556 q = 2) : d380596 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47556, d380596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39981 q selected
    | true =>
      simp only [d47556, d380596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47557 q = 2) : d380597 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47557, d380597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47557, d380597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47558 q = 2) : d380598 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47558, d380598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47558, d380598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47559 q = 2) : d380599 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47559, d380599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47559, d380599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47560 q = 2) : d380600 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47560, d380600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47560, d380600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47561 q = 2) : d380601 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47561, d380601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47561, d380601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39983 (p : Pattern) (selected : d47611 p = 1) : d47611 p = 1 := by
  have h0 (q : Pattern) (selected : d47611 q = 1) : d47611 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro39984 (p : Pattern) (selected : d380929 p = 0) : d380974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d47465 q = 0) : d380015 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47465, d380015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33045 q selected
    | true =>
      simp only [d47465, d380015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380926 q = 0) : d380971 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380926, d380971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380926, d380971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380927 q = 0) : d380972 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380927, d380972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380927, d380972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380928 q = 0) : d380973 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380928, d380973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380928, d380973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380929 q = 0) : d380974 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380929, d380974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380929, d380974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39985 (p : Pattern) (selected : d380934 p = 0) : d380979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380930 q = 0) : d380975 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380930, d380975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39984 q selected
    | true =>
      simp only [d380930, d380975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380931 q = 0) : d380976 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380931, d380976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380931, d380976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380932 q = 0) : d380977 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380932, d380977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380932, d380977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380933 q = 0) : d380978 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380933, d380978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380933, d380978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380934 q = 0) : d380979 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380934, d380979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380934, d380979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39986 (p : Pattern) (selected : d380940 p = 0) : d380985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380935 q = 0) : d380980 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380935, d380980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39985 q selected
    | true =>
      simp only [d380935, d380980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380936 q = 0) : d380981 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380936, d380981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380936, d380981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380937 q = 0) : d380982 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380937, d380982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380937, d380982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380938 q = 0) : d380983 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380938, d380983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380938, d380983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380939 q = 0) : d380984 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380939, d380984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380939, d380984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380940 q = 0) : d380985 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380940, d380985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380940, d380985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39987 (p : Pattern) (selected : d380946 p = 0) : d380991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380941 q = 0) : d380986 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380941, d380986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39986 q selected
    | true =>
      simp only [d380941, d380986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380942 q = 0) : d380987 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380942, d380987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380942, d380987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380943 q = 0) : d380988 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380943, d380988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380943, d380988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380944 q = 0) : d380989 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380944, d380989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380944, d380989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380945 q = 0) : d380990 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380945, d380990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380945, d380990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380946 q = 0) : d380991 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380946, d380991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380946, d380991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39988 (p : Pattern) (selected : d380952 p = 0) : d380997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380947 q = 0) : d380992 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380947, d380992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39987 q selected
    | true =>
      simp only [d380947, d380992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380948 q = 0) : d380993 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380948, d380993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380948, d380993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380949 q = 0) : d380994 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380949, d380994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380949, d380994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380950 q = 0) : d380995 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380950, d380995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380950, d380995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380951 q = 0) : d380996 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380951, d380996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380951, d380996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380952 q = 0) : d380997 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380952, d380997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380952, d380997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39989 (p : Pattern) (selected : d380958 p = 0) : d381003 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380953 q = 0) : d380998 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380953, d380998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39988 q selected
    | true =>
      simp only [d380953, d380998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380954 q = 0) : d380999 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380954, d380999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380954, d380999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380955 q = 0) : d381000 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380955, d381000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380955, d381000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380956 q = 0) : d381001 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380956, d381001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380956, d381001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380957 q = 0) : d381002 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380957, d381002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380957, d381002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380958 q = 0) : d381003 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380958, d381003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380958, d381003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39990 (p : Pattern) (selected : d380964 p = 0) : d381009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380959 q = 0) : d381004 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380959, d381004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39989 q selected
    | true =>
      simp only [d380959, d381004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380960 q = 0) : d381005 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380960, d381005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380960, d381005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380961 q = 0) : d381006 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380961, d381006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380961, d381006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380962 q = 0) : d381007 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380962, d381007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380962, d381007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380963 q = 0) : d381008 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380963, d381008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380963, d381008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380964 q = 0) : d381009 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380964, d381009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380964, d381009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39991 (p : Pattern) (selected : d380970 p = 0) : d381015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d380965 q = 0) : d381010 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380965, d381010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39990 q selected
    | true =>
      simp only [d380965, d381010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380966 q = 0) : d381011 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380966, d381011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380966, d381011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380967 q = 0) : d381012 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380967, d381012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380967, d381012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380968 q = 0) : d381013 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380968, d381013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380968, d381013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380969 q = 0) : d381014 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380969, d381014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380969, d381014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380970 q = 0) : d381015 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380970, d381015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380970, d381015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39992 (p : Pattern) (selected : d380929 p = 1) : d381019 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d47465 q = 1) : d380063 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47465, d380063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33452 q selected
    | true =>
      simp only [d47465, d380063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380926 q = 1) : d381016 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380926, d381016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380926, d381016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380927 q = 1) : d381017 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380927, d381017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380927, d381017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380928 q = 1) : d381018 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380928, d381018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380928, d381018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380929 q = 1) : d381019 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380929, d381019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380929, d381019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39993 (p : Pattern) (selected : d380934 p = 1) : d381024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380930 q = 1) : d381020 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380930, d381020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39992 q selected
    | true =>
      simp only [d380930, d381020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380931 q = 1) : d381021 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380931, d381021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380931, d381021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380932 q = 1) : d381022 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380932, d381022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380932, d381022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380933 q = 1) : d381023 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380933, d381023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380933, d381023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380934 q = 1) : d381024 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380934, d381024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380934, d381024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro39994 (p : Pattern) (selected : d380940 p = 1) : d381030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380935 q = 1) : d381025 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380935, d381025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39993 q selected
    | true =>
      simp only [d380935, d381025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380936 q = 1) : d381026 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380936, d381026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380936, d381026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380937 q = 1) : d381027 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380937, d381027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380937, d381027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380938 q = 1) : d381028 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380938, d381028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380938, d381028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380939 q = 1) : d381029 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380939, d381029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380939, d381029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380940 q = 1) : d381030 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380940, d381030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380940, d381030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39995 (p : Pattern) (selected : d380946 p = 1) : d381036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380941 q = 1) : d381031 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380941, d381031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39994 q selected
    | true =>
      simp only [d380941, d381031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380942 q = 1) : d381032 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380942, d381032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380942, d381032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380943 q = 1) : d381033 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380943, d381033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380943, d381033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380944 q = 1) : d381034 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380944, d381034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380944, d381034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380945 q = 1) : d381035 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380945, d381035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380945, d381035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380946 q = 1) : d381036 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380946, d381036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380946, d381036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39996 (p : Pattern) (selected : d380952 p = 1) : d381042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380947 q = 1) : d381037 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380947, d381037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39995 q selected
    | true =>
      simp only [d380947, d381037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380948 q = 1) : d381038 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380948, d381038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380948, d381038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380949 q = 1) : d381039 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380949, d381039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380949, d381039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380950 q = 1) : d381040 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380950, d381040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380950, d381040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380951 q = 1) : d381041 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380951, d381041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380951, d381041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380952 q = 1) : d381042 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380952, d381042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380952, d381042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39997 (p : Pattern) (selected : d380958 p = 1) : d381048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380953 q = 1) : d381043 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380953, d381043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39996 q selected
    | true =>
      simp only [d380953, d381043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380954 q = 1) : d381044 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380954, d381044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380954, d381044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380955 q = 1) : d381045 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380955, d381045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380955, d381045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380956 q = 1) : d381046 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380956, d381046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380956, d381046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380957 q = 1) : d381047 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380957, d381047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380957, d381047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380958 q = 1) : d381048 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380958, d381048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380958, d381048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39998 (p : Pattern) (selected : d380964 p = 1) : d381054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380959 q = 1) : d381049 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380959, d381049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39997 q selected
    | true =>
      simp only [d380959, d381049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380960 q = 1) : d381050 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380960, d381050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380960, d381050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380961 q = 1) : d381051 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380961, d381051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380961, d381051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380962 q = 1) : d381052 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380962, d381052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380962, d381052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380963 q = 1) : d381053 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380963, d381053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380963, d381053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380964 q = 1) : d381054 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380964, d381054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380964, d381054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro39999 (p : Pattern) (selected : d380970 p = 1) : d381060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d380965 q = 1) : d381055 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380965, d381055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39998 q selected
    | true =>
      simp only [d380965, d381055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d380966 q = 1) : d381056 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380966, d381056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d380966, d381056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d380967 q = 1) : d381057 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380967, d381057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d380967, d381057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d380968 q = 1) : d381058 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380968, d381058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d380968, d381058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d380969 q = 1) : d381059 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380969, d381059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d380969, d381059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d380970 q = 1) : d381060 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380970, d381060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d380970, d381060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
