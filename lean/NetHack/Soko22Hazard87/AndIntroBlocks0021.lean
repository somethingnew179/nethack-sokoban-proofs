import NetHack.Soko22Hazard87.AndIntroBlocks0020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro5250 (p : Pattern) (ha : d54238 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5249 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5251 (p : Pattern) (ha : d54243 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53484 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53485 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53495 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53495, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54243 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54243, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5252 (p : Pattern) (ha : d54249 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5251 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5253 (p : Pattern) (ha : d54255 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5242 q ha hb
    | true =>
      simp only [d54212, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5244 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5246 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5248 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5250 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5252 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5254 (p : Pattern) (ha : d54261 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5253 q ha hb
    | true =>
      simp only [d54256, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5255 (p : Pattern) (ha : d54267 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5254 q ha hb
    | true =>
      simp only [d54262, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5256 (p : Pattern) (ha : d54273 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5255 q ha hb
    | true =>
      simp only [d54268, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5257 (p : Pattern) (ha : d54279 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5256 q ha hb
    | true =>
      simp only [d54274, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5258 (p : Pattern) (ha : d54285 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5257 q ha hb
    | true =>
      simp only [d54280, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5259 (p : Pattern) (ha : d54291 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5258 q ha hb
    | true =>
      simp only [d54286, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5260 (p : Pattern) (ha : d54297 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5259 q ha hb
    | true =>
      simp only [d54292, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5261 (p : Pattern) (ha : d54298 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51649 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51650 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51651 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51651, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54298 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54298, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54298, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5262 (p : Pattern) (ha : d54304 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51666 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51667 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51670 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51671 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51671, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54304 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54304, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54304, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5263 (p : Pattern) (ha : d54310 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54299 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54299, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54299, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5261 q ha hb
  have h3 (q : Pattern) (ha : d54300 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54300, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54300, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54301 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54301, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54301, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54302 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54302, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54302, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54303 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54303, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54303, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54305 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54305, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54305, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5262 q ha hb
  have h8 (q : Pattern) (ha : d54306 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54306, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54306, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54307 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54307, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54307, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54308 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54308, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54308, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54309 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54309, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54309, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54310 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54310, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54310, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5264 (p : Pattern) (ha : d54311 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51691 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51692 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51695 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51696 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51696, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54311 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54311, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54311, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5265 (p : Pattern) (ha : d54317 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54312 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54312, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54312, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5264 q ha hb
  have h2 (q : Pattern) (ha : d54313 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54313, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54313, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54314 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54314, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54314, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54315 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54315, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54315, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54316 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54316, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54316, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54317 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54317, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54317, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5266 (p : Pattern) (ha : d54319 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51717 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51718 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51721 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51722 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51722, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54319 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54319, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54319, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5267 (p : Pattern) (ha : d54325 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54320 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54320, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54320, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5266 q ha hb
  have h2 (q : Pattern) (ha : d54321 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54321, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54321, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54322 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54322, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54322, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54323 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54323, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54323, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54324 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54324, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54324, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54325 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54325, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54325, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5268 (p : Pattern) (ha : d54328 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51744 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51745 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51748 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51749 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51749, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54328 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54328, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54328, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5269 (p : Pattern) (ha : d54334 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54329 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54329, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54329, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5268 q ha hb
  have h2 (q : Pattern) (ha : d54330 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54330, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54330, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54331 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54331, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54331, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54332 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54332, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54332, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54333 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54333, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54333, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54334 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54334, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54334, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5270 (p : Pattern) (ha : d54338 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51772 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51773 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51776 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51777 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51777, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54338 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54338, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54338, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5271 (p : Pattern) (ha : d54344 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54339 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54339, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54339, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5270 q ha hb
  have h2 (q : Pattern) (ha : d54340 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54340, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54340, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54341 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54341, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54341, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54342 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54342, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54342, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54343 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54343, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54343, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54344 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54344, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54344, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5272 (p : Pattern) (ha : d54349 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51801 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51802 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51805 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51806 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51806, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54349 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54349, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54349, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h10 p ha hb
theorem andIntro5273 (p : Pattern) (ha : d54355 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54350 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54350, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54350, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5272 q ha hb
  have h2 (q : Pattern) (ha : d54351 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54351, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54351, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54352 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54352, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54352, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54353 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54353, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54353, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54354 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54354, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54354, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54355 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54355, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54355, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5274 (p : Pattern) (ha : d54361 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54318 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54318, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5263 q ha hb
    | true =>
      simp only [d54318, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5265 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54326 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54326, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54326, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5267 q ha hb
  have h3 (q : Pattern) (ha : d54327 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54327, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54327, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54335 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54335, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54335, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5269 q ha hb
  have h5 (q : Pattern) (ha : d54336 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54336, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54336, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54337 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54337, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54337, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54345 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54345, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54345, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5271 q ha hb
  have h8 (q : Pattern) (ha : d54346 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54346, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54346, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54347 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54347, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54347, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54348 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54348, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54348, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54356 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54356, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54356, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5273 q ha hb
  have h12 (q : Pattern) (ha : d54357 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54357, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54357, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54358 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54358, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54358, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54359 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54359, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54359, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54360 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54360, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54360, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54361 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54361, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54361, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5275 (p : Pattern) (ha : d54367 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54362 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54362, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5274 q ha hb
    | true =>
      simp only [d54362, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54363 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54363, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54363, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54364 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54364, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54364, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54365 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54365, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54365, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54366 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54366, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54366, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54367 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54367, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54367, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5276 (p : Pattern) (ha : d54373 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54368 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54368, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5275 q ha hb
    | true =>
      simp only [d54368, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54369 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54369, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54369, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54370 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54370, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54370, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54371 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54371, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54371, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54372 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54372, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54372, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54373 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54373, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54373, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5277 (p : Pattern) (ha : d54379 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54374 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54374, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5276 q ha hb
    | true =>
      simp only [d54374, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54375 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54375, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54375, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54376 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54376, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54376, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54377 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54377, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54377, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54378 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54378, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54378, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54379 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54379, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54379, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5278 (p : Pattern) (ha : d54385 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54380 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54380, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5277 q ha hb
    | true =>
      simp only [d54380, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54381 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54381, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54381, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54382 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54382, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54382, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54383 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54383, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54383, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54384 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54384, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54384, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54385 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54385, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54385, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5279 (p : Pattern) (ha : d54391 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54386 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54386, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5278 q ha hb
    | true =>
      simp only [d54386, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54387 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54387, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54387, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54388 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54388, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54388, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54389 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54389, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54389, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54390 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54390, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54390, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54391 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54391, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54391, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5280 (p : Pattern) (ha : d54397 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54392 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54392, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5279 q ha hb
    | true =>
      simp only [d54392, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54393 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54393, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54393, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54394 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54394, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54394, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54395 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54395, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54395, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54396 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54396, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54396, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54397 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54397, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54397, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5281 (p : Pattern) (ha : d54403 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54398 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54398, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5280 q ha hb
    | true =>
      simp only [d54398, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54399 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54399, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54399, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54400 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54400, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54400, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54401 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54401, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54401, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54402 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54402, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54402, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54403 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54403, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54403, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5282 (p : Pattern) (ha : d3324 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3319 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1915 q ha hb
    | true =>
      simp only [d3319, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3320 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3321 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3322 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3323 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d3324 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5283 (p : Pattern) (ha : d61544 p = 1) (hb : d62374 p = 1) : d59645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d3329, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3330 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3331 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61539 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61539, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1920 q ha hb
    | true =>
      simp only [d61539, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d214 q = 1) (hb : d62374 q = 1) : d214 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d61540 q = 1) (hb : d62374 q = 1) : d59641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61540, d59641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61540, d59641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61541 q = 1) (hb : d62374 q = 1) : d59642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61541, d59642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61541, d59642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61542 q = 1) (hb : d62374 q = 1) : d59643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61542, d59643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61542, d59643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61543 q = 1) (hb : d62374 q = 1) : d59644 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61543, d59644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61543, d59644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61544 q = 1) (hb : d62374 q = 1) : d59645 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61544, d59645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61544, d59645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5284 (p : Pattern) (ha : d61555 p = 1) (hb : d62374 p = 1) : d73366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d3343, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3345 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61550 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1926 q ha hb
    | true =>
      simp only [d61550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3347 q = 1) (hb : d62374 q = 1) : d73361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d62374, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1925 q ha hb
    | true =>
      simp only [d3347, d62374, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61551 q = 1) (hb : d62374 q = 1) : d73362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61551, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61551, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61552 q = 1) (hb : d62374 q = 1) : d73363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61552, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61552, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61553 q = 1) (hb : d62374 q = 1) : d73364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61553, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61553, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61554 q = 1) (hb : d62374 q = 1) : d73365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61554, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61554, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61555 q = 1) (hb : d62374 q = 1) : d73366 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61555, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61555, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5285 (p : Pattern) (ha : d61561 p = 1) (hb : d62374 p = 1) : d73372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5282 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61545 q = 1) (hb : d62374 q = 1) : d59646 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61545, d59646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61545, d59646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5283 q ha hb
  have h6 (q : Pattern) (ha : d61546 q = 1) (hb : d62374 q = 1) : d59647 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61546, d59647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61546, d59647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61547 q = 1) (hb : d62374 q = 1) : d59648 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61547, d59648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61547, d59648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61548 q = 1) (hb : d62374 q = 1) : d59649 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61548, d59649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61548, d59649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61549 q = 1) (hb : d62374 q = 1) : d59650 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61549, d59650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61549, d59650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61556 q = 1) (hb : d62374 q = 1) : d73367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61556, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61556, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5284 q ha hb
  have h11 (q : Pattern) (ha : d61557 q = 1) (hb : d62374 q = 1) : d73368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61557, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61557, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61558 q = 1) (hb : d62374 q = 1) : d73369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61558, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61558, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61559 q = 1) (hb : d62374 q = 1) : d73370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61559, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61559, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61560 q = 1) (hb : d62374 q = 1) : d73371 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61560, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61560, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61561 q = 1) (hb : d62374 q = 1) : d73372 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61561, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61561, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5286 (p : Pattern) (ha : d61567 p = 1) (hb : d62374 p = 1) : d73378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d3359, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3361 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61562 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61562, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1934 q ha hb
    | true =>
      simp only [d61562, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3363 q = 1) (hb : d62374 q = 1) : d73373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d62374, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1932 q ha hb
    | true =>
      simp only [d3363, d62374, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61563 q = 1) (hb : d62374 q = 1) : d73374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61563, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61563, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61564 q = 1) (hb : d62374 q = 1) : d73375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61564, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61564, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61565 q = 1) (hb : d62374 q = 1) : d73376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61565, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61565, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61566 q = 1) (hb : d62374 q = 1) : d73377 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61566, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61566, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61567 q = 1) (hb : d62374 q = 1) : d73378 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61567, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61567, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5287 (p : Pattern) (ha : d61573 p = 1) (hb : d62374 p = 1) : d73384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61568 q = 1) (hb : d62374 q = 1) : d73379 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61568, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61568, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5286 q ha hb
  have h2 (q : Pattern) (ha : d61569 q = 1) (hb : d62374 q = 1) : d73380 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61569, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61569, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61570 q = 1) (hb : d62374 q = 1) : d73381 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61570, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61570, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61571 q = 1) (hb : d62374 q = 1) : d73382 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61571, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61571, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61572 q = 1) (hb : d62374 q = 1) : d73383 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61572, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61572, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61573 q = 1) (hb : d62374 q = 1) : d73384 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61573, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61573, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5288 (p : Pattern) (ha : d61580 p = 1) (hb : d62374 p = 1) : d73391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d3376, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3378 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61575 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61575, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1942 q ha hb
    | true =>
      simp only [d61575, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3380 q = 1) (hb : d62374 q = 1) : d73386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d62374, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1940 q ha hb
    | true =>
      simp only [d3380, d62374, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61576 q = 1) (hb : d62374 q = 1) : d73387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61576, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61576, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61577 q = 1) (hb : d62374 q = 1) : d73388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61577, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61577, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61578 q = 1) (hb : d62374 q = 1) : d73389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61578, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61578, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61579 q = 1) (hb : d62374 q = 1) : d73390 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61579, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61579, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61580 q = 1) (hb : d62374 q = 1) : d73391 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61580, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61580, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5289 (p : Pattern) (ha : d61586 p = 1) (hb : d62374 p = 1) : d73397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61581 q = 1) (hb : d62374 q = 1) : d73392 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61581, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61581, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5288 q ha hb
  have h2 (q : Pattern) (ha : d61582 q = 1) (hb : d62374 q = 1) : d73393 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61582, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61582, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61583 q = 1) (hb : d62374 q = 1) : d73394 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61583, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61583, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61584 q = 1) (hb : d62374 q = 1) : d73395 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61584, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61584, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61585 q = 1) (hb : d62374 q = 1) : d73396 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61585, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61585, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61586 q = 1) (hb : d62374 q = 1) : d73397 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61586, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61586, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5290 (p : Pattern) (ha : d61594 p = 1) (hb : d62374 p = 1) : d73405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d3394, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3396 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61589 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61589, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1950 q ha hb
    | true =>
      simp only [d61589, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3398 q = 1) (hb : d62374 q = 1) : d73400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d62374, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1948 q ha hb
    | true =>
      simp only [d3398, d62374, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61590 q = 1) (hb : d62374 q = 1) : d73401 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61590, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61590, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61591 q = 1) (hb : d62374 q = 1) : d73402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61591, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61591, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61592 q = 1) (hb : d62374 q = 1) : d73403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61592, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61592, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61593 q = 1) (hb : d62374 q = 1) : d73404 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61593, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61593, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61594 q = 1) (hb : d62374 q = 1) : d73405 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61594, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61594, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5291 (p : Pattern) (ha : d61600 p = 1) (hb : d62374 p = 1) : d73411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61595 q = 1) (hb : d62374 q = 1) : d73406 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61595, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61595, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5290 q ha hb
  have h2 (q : Pattern) (ha : d61596 q = 1) (hb : d62374 q = 1) : d73407 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61596, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61596, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61597 q = 1) (hb : d62374 q = 1) : d73408 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61597, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61597, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61598 q = 1) (hb : d62374 q = 1) : d73409 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61598, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61598, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61599 q = 1) (hb : d62374 q = 1) : d73410 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61599, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61599, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61600 q = 1) (hb : d62374 q = 1) : d73411 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61600, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61600, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5292 (p : Pattern) (ha : d61609 p = 1) (hb : d62374 p = 1) : d73420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d3413, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3415 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61604 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61604, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1958 q ha hb
    | true =>
      simp only [d61604, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3417 q = 1) (hb : d62374 q = 1) : d73415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d62374, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1956 q ha hb
    | true =>
      simp only [d3417, d62374, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61605 q = 1) (hb : d62374 q = 1) : d73416 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61605, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61605, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61606 q = 1) (hb : d62374 q = 1) : d73417 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61606, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61606, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61607 q = 1) (hb : d62374 q = 1) : d73418 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61607, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61607, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61608 q = 1) (hb : d62374 q = 1) : d73419 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61608, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61608, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61609 q = 1) (hb : d62374 q = 1) : d73420 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61609, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61609, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5293 (p : Pattern) (ha : d61615 p = 1) (hb : d62374 p = 1) : d73426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61610 q = 1) (hb : d62374 q = 1) : d73421 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61610, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61610, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5292 q ha hb
  have h2 (q : Pattern) (ha : d61611 q = 1) (hb : d62374 q = 1) : d73422 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61611, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61611, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61612 q = 1) (hb : d62374 q = 1) : d73423 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61612, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61612, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61613 q = 1) (hb : d62374 q = 1) : d73424 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61613, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61613, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61614 q = 1) (hb : d62374 q = 1) : d73425 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61614, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61614, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61615 q = 1) (hb : d62374 q = 1) : d73426 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61615, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61615, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5294 (p : Pattern) (ha : d61625 p = 1) (hb : d62374 p = 1) : d73436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d3433, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3435 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61620 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61620, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1966 q ha hb
    | true =>
      simp only [d61620, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d3437 q = 1) (hb : d62374 q = 1) : d73431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d62374, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1964 q ha hb
    | true =>
      simp only [d3437, d62374, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d61621 q = 1) (hb : d62374 q = 1) : d73432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61621, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61621, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61622 q = 1) (hb : d62374 q = 1) : d73433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61622, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61622, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d61623 q = 1) (hb : d62374 q = 1) : d73434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61623, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61623, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61624 q = 1) (hb : d62374 q = 1) : d73435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61624, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d61624, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d61625 q = 1) (hb : d62374 q = 1) : d73436 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61625, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61625, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro5295 (p : Pattern) (ha : d61631 p = 1) (hb : d62374 p = 1) : d73442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61626 q = 1) (hb : d62374 q = 1) : d73437 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61626, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61626, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5294 q ha hb
  have h2 (q : Pattern) (ha : d61627 q = 1) (hb : d62374 q = 1) : d73438 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61627, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61627, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61628 q = 1) (hb : d62374 q = 1) : d73439 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61628, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61628, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61629 q = 1) (hb : d62374 q = 1) : d73440 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61629, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61629, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61630 q = 1) (hb : d62374 q = 1) : d73441 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61630, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61630, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61631 q = 1) (hb : d62374 q = 1) : d73442 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61631, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61631, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5296 (p : Pattern) (ha : d61637 p = 1) (hb : d62374 p = 1) : d73448 p = 1 := by
  have h0 (q : Pattern) (ha : d61574 q = 1) (hb : d62374 q = 1) : d73385 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61574, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5285 q ha hb
    | true =>
      simp only [d61574, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5287 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61587 q = 1) (hb : d62374 q = 1) : d73398 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61587, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61587, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5289 q ha hb
  have h3 (q : Pattern) (ha : d61588 q = 1) (hb : d62374 q = 1) : d73399 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61588, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61588, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61601 q = 1) (hb : d62374 q = 1) : d73412 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61601, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61601, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5291 q ha hb
  have h5 (q : Pattern) (ha : d61602 q = 1) (hb : d62374 q = 1) : d73413 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61602, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61602, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61603 q = 1) (hb : d62374 q = 1) : d73414 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61603, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61603, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61616 q = 1) (hb : d62374 q = 1) : d73427 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61616, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61616, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5293 q ha hb
  have h8 (q : Pattern) (ha : d61617 q = 1) (hb : d62374 q = 1) : d73428 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61617, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61617, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61618 q = 1) (hb : d62374 q = 1) : d73429 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61618, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61618, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61619 q = 1) (hb : d62374 q = 1) : d73430 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61619, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61619, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61632 q = 1) (hb : d62374 q = 1) : d73443 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61632, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61632, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5295 q ha hb
  have h12 (q : Pattern) (ha : d61633 q = 1) (hb : d62374 q = 1) : d73444 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61633, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61633, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61634 q = 1) (hb : d62374 q = 1) : d73445 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61634, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61634, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61635 q = 1) (hb : d62374 q = 1) : d73446 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61635, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61635, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61636 q = 1) (hb : d62374 q = 1) : d73447 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61636, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61636, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61637 q = 1) (hb : d62374 q = 1) : d73448 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61637, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61637, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5297 (p : Pattern) (ha : d61643 p = 1) (hb : d62374 p = 1) : d73454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61638 q = 1) (hb : d62374 q = 1) : d73449 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61638, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5296 q ha hb
    | true =>
      simp only [d61638, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61639 q = 1) (hb : d62374 q = 1) : d73450 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61639, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61639, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61640 q = 1) (hb : d62374 q = 1) : d73451 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61640, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61640, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61641 q = 1) (hb : d62374 q = 1) : d73452 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61641, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61641, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61642 q = 1) (hb : d62374 q = 1) : d73453 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61642, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61642, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61643 q = 1) (hb : d62374 q = 1) : d73454 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61643, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61643, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5298 (p : Pattern) (ha : d61649 p = 1) (hb : d62374 p = 1) : d73460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61644 q = 1) (hb : d62374 q = 1) : d73455 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61644, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5297 q ha hb
    | true =>
      simp only [d61644, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61645 q = 1) (hb : d62374 q = 1) : d73456 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61645, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61645, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61646 q = 1) (hb : d62374 q = 1) : d73457 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61646, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61646, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61647 q = 1) (hb : d62374 q = 1) : d73458 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61647, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61647, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61648 q = 1) (hb : d62374 q = 1) : d73459 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61648, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61648, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61649 q = 1) (hb : d62374 q = 1) : d73460 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61649, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61649, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5299 (p : Pattern) (ha : d61655 p = 1) (hb : d62374 p = 1) : d73466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61650 q = 1) (hb : d62374 q = 1) : d73461 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61650, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5298 q ha hb
    | true =>
      simp only [d61650, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61651 q = 1) (hb : d62374 q = 1) : d73462 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61651, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61651, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61652 q = 1) (hb : d62374 q = 1) : d73463 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61652, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61652, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61653 q = 1) (hb : d62374 q = 1) : d73464 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61653, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61653, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61654 q = 1) (hb : d62374 q = 1) : d73465 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61654, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61654, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61655 q = 1) (hb : d62374 q = 1) : d73466 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61655, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61655, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5300 (p : Pattern) (ha : d61661 p = 1) (hb : d62374 p = 1) : d73472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61656 q = 1) (hb : d62374 q = 1) : d73467 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61656, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5299 q ha hb
    | true =>
      simp only [d61656, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61657 q = 1) (hb : d62374 q = 1) : d73468 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61657, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61657, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61658 q = 1) (hb : d62374 q = 1) : d73469 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61658, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61658, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61659 q = 1) (hb : d62374 q = 1) : d73470 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61659, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61659, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61660 q = 1) (hb : d62374 q = 1) : d73471 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61660, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61660, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61661 q = 1) (hb : d62374 q = 1) : d73472 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61661, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61661, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5301 (p : Pattern) (ha : d61667 p = 1) (hb : d62374 p = 1) : d73478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61662 q = 1) (hb : d62374 q = 1) : d73473 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61662, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5300 q ha hb
    | true =>
      simp only [d61662, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61663 q = 1) (hb : d62374 q = 1) : d73474 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61663, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61663, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61664 q = 1) (hb : d62374 q = 1) : d73475 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61664, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61664, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61665 q = 1) (hb : d62374 q = 1) : d73476 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61665, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61665, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61666 q = 1) (hb : d62374 q = 1) : d73477 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61666, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61666, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61667 q = 1) (hb : d62374 q = 1) : d73478 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61667, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61667, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5302 (p : Pattern) (ha : d61673 p = 1) (hb : d62374 p = 1) : d73484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61668 q = 1) (hb : d62374 q = 1) : d73479 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61668, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5301 q ha hb
    | true =>
      simp only [d61668, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61669 q = 1) (hb : d62374 q = 1) : d73480 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61669, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61669, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61670 q = 1) (hb : d62374 q = 1) : d73481 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61670, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61670, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61671 q = 1) (hb : d62374 q = 1) : d73482 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61671, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61671, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61672 q = 1) (hb : d62374 q = 1) : d73483 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61672, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61672, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61673 q = 1) (hb : d62374 q = 1) : d73484 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61673, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61673, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5303 (p : Pattern) (ha : d61679 p = 1) (hb : d62374 p = 1) : d73490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61674 q = 1) (hb : d62374 q = 1) : d73485 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61674, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5302 q ha hb
    | true =>
      simp only [d61674, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61675 q = 1) (hb : d62374 q = 1) : d73486 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61675, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61675, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61676 q = 1) (hb : d62374 q = 1) : d73487 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61676, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61676, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61677 q = 1) (hb : d62374 q = 1) : d73488 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61677, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61677, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61678 q = 1) (hb : d62374 q = 1) : d73489 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61678, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61678, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61679 q = 1) (hb : d62374 q = 1) : d73490 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61679, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61679, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5304 (p : Pattern) (ha : d59645 p = 1) (hb : d62395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62390 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59641 q = 1) (hb : d62391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59641, d62391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59641, d62391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59642 q = 1) (hb : d62392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59642, d62392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59642, d62392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d59643 q = 1) (hb : d62393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59643, d62393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59643, d62393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59644 q = 1) (hb : d62394 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59644, d62394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59644, d62394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d59645 q = 1) (hb : d62395 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59645, d62395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d59645, d62395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h8 p ha hb
theorem andIntro5305 (p : Pattern) (ha : d62409 p = 1) (hb : d73366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62401 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62404 q = 1) (hb : d73361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62404, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro697 q hb ha
    | true =>
      simp only [d62404, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62405 q = 1) (hb : d73362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62405, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62405, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62406 q = 1) (hb : d73363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62406, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62406, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62407 q = 1) (hb : d73364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62407, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62407, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62408 q = 1) (hb : d73365 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62408, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62408, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62409 q = 1) (hb : d73366 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62409, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62409, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5306 (p : Pattern) (ha : d62415 p = 1) (hb : d73372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59646 q = 1) (hb : d62396 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59646, d62396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59646, d62396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5304 q ha hb
  have h3 (q : Pattern) (ha : d59647 q = 1) (hb : d62397 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59647, d62397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59647, d62397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59648 q = 1) (hb : d62398 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59648, d62398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59648, d62398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59649 q = 1) (hb : d62399 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59649, d62399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59649, d62399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59650 q = 1) (hb : d62400 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59650, d62400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59650, d62400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62410 q = 1) (hb : d73367 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62410, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62410, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5305 q ha hb
  have h8 (q : Pattern) (ha : d62411 q = 1) (hb : d73368 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62411, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62411, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62412 q = 1) (hb : d73369 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62412, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62412, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62413 q = 1) (hb : d73370 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62413, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62413, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62414 q = 1) (hb : d73371 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62414, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62414, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62415 q = 1) (hb : d73372 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62415, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d62415, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5307 (p : Pattern) (ha : d62425 p = 1) (hb : d73378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62419 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62420 q = 1) (hb : d73373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62420, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro700 q hb ha
    | true =>
      simp only [d62420, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62421 q = 1) (hb : d73374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62421, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62421, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62422 q = 1) (hb : d73375 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62422, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62422, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62423 q = 1) (hb : d73376 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62423, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62423, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62424 q = 1) (hb : d73377 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62424, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62424, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62425 q = 1) (hb : d73378 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62425, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62425, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5308 (p : Pattern) (ha : d62431 p = 1) (hb : d73384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62426 q = 1) (hb : d73379 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62426, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62426, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5307 q ha hb
  have h2 (q : Pattern) (ha : d62427 q = 1) (hb : d73380 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62427, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62427, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62428 q = 1) (hb : d73381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62428, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62428, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62429 q = 1) (hb : d73382 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62429, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62429, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62430 q = 1) (hb : d73383 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62430, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62430, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62431 q = 1) (hb : d73384 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62431, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62431, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5309 (p : Pattern) (ha : d62442 p = 1) (hb : d73391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62433 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62437 q = 1) (hb : d73386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62437, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro703 q hb ha
    | true =>
      simp only [d62437, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62438 q = 1) (hb : d73387 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62438, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62438, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62439 q = 1) (hb : d73388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62439, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62439, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62440 q = 1) (hb : d73389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62440, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62440, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62441 q = 1) (hb : d73390 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62441, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62441, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62442 q = 1) (hb : d73391 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62442, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62442, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5310 (p : Pattern) (ha : d62448 p = 1) (hb : d73397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62443 q = 1) (hb : d73392 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62443, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62443, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5309 q ha hb
  have h2 (q : Pattern) (ha : d62444 q = 1) (hb : d73393 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62444, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62444, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62445 q = 1) (hb : d73394 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62445, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62445, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62446 q = 1) (hb : d73395 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62446, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62446, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62447 q = 1) (hb : d73396 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62447, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62447, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62448 q = 1) (hb : d73397 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62448, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62448, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5311 (p : Pattern) (ha : d62460 p = 1) (hb : d73405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62454 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62455 q = 1) (hb : d73400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62455, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro706 q hb ha
    | true =>
      simp only [d62455, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62456 q = 1) (hb : d73401 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62456, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62456, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62457 q = 1) (hb : d73402 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62457, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62457, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62458 q = 1) (hb : d73403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62458, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62458, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62459 q = 1) (hb : d73404 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62459, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62459, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62460 q = 1) (hb : d73405 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62460, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62460, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5312 (p : Pattern) (ha : d62466 p = 1) (hb : d73411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62461 q = 1) (hb : d73406 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62461, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62461, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5311 q ha hb
  have h2 (q : Pattern) (ha : d62462 q = 1) (hb : d73407 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62462, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62462, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62463 q = 1) (hb : d73408 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62463, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62463, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62464 q = 1) (hb : d73409 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62464, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62464, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62465 q = 1) (hb : d73410 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62465, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62465, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62466 q = 1) (hb : d73411 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62466, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62466, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5313 (p : Pattern) (ha : d62479 p = 1) (hb : d73420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62470 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62474 q = 1) (hb : d73415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62474, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro709 q hb ha
    | true =>
      simp only [d62474, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62475 q = 1) (hb : d73416 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62475, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62475, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62476 q = 1) (hb : d73417 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62476, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62476, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62477 q = 1) (hb : d73418 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62477, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62477, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62478 q = 1) (hb : d73419 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62478, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62478, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62479 q = 1) (hb : d73420 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62479, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62479, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5314 (p : Pattern) (ha : d62485 p = 1) (hb : d73426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62480 q = 1) (hb : d73421 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62480, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62480, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5313 q ha hb
  have h2 (q : Pattern) (ha : d62481 q = 1) (hb : d73422 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62481, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62481, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62482 q = 1) (hb : d73423 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62482, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62482, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62483 q = 1) (hb : d73424 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62483, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62483, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62484 q = 1) (hb : d73425 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62484, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62484, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62485 q = 1) (hb : d73426 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62485, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62485, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5315 (p : Pattern) (ha : d62499 p = 1) (hb : d73436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62490 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d62493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62494 q = 1) (hb : d73431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62494, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q hb ha
    | true =>
      simp only [d62494, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d62495 q = 1) (hb : d73432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62495, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62495, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62496 q = 1) (hb : d73433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62496, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62496, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62497 q = 1) (hb : d73434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62497, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62497, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62498 q = 1) (hb : d73435 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62498, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62498, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d62499 q = 1) (hb : d73436 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62499, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62499, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5316 (p : Pattern) (ha : d62505 p = 1) (hb : d73442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62500 q = 1) (hb : d73437 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62500, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62500, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5315 q ha hb
  have h2 (q : Pattern) (ha : d62501 q = 1) (hb : d73438 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62501, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62501, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62502 q = 1) (hb : d73439 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62502, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62502, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62503 q = 1) (hb : d73440 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62503, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62503, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62504 q = 1) (hb : d73441 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62504, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62504, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62505 q = 1) (hb : d73442 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62505, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62505, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5317 (p : Pattern) (ha : d62511 p = 1) (hb : d73448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62432 q = 1) (hb : d73385 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62432, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5306 q ha hb
    | true =>
      simp only [d62432, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5308 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62449 q = 1) (hb : d73398 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62449, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62449, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5310 q ha hb
  have h3 (q : Pattern) (ha : d62450 q = 1) (hb : d73399 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62450, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62450, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62467 q = 1) (hb : d73412 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62467, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62467, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5312 q ha hb
  have h5 (q : Pattern) (ha : d62468 q = 1) (hb : d73413 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62468, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62468, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62469 q = 1) (hb : d73414 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62469, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62469, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62486 q = 1) (hb : d73427 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62486, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62486, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5314 q ha hb
  have h8 (q : Pattern) (ha : d62487 q = 1) (hb : d73428 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62487, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62487, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62488 q = 1) (hb : d73429 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62488, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62488, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62489 q = 1) (hb : d73430 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62489, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62489, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62506 q = 1) (hb : d73443 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62506, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62506, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5316 q ha hb
  have h12 (q : Pattern) (ha : d62507 q = 1) (hb : d73444 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62507, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62507, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62508 q = 1) (hb : d73445 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62508, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62508, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62509 q = 1) (hb : d73446 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62509, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62509, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62510 q = 1) (hb : d73447 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62510, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62510, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62511 q = 1) (hb : d73448 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62511, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62511, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5318 (p : Pattern) (ha : d62517 p = 1) (hb : d73454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62512 q = 1) (hb : d73449 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62512, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5317 q ha hb
    | true =>
      simp only [d62512, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62513 q = 1) (hb : d73450 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62513, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62513, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62514 q = 1) (hb : d73451 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62514, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62514, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62515 q = 1) (hb : d73452 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62515, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62515, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62516 q = 1) (hb : d73453 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62516, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62516, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62517 q = 1) (hb : d73454 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62517, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62517, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5319 (p : Pattern) (ha : d62523 p = 1) (hb : d73460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62518 q = 1) (hb : d73455 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62518, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5318 q ha hb
    | true =>
      simp only [d62518, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62519 q = 1) (hb : d73456 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62519, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62519, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62520 q = 1) (hb : d73457 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62520, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62520, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62521 q = 1) (hb : d73458 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62521, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62521, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62522 q = 1) (hb : d73459 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62522, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62522, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62523 q = 1) (hb : d73460 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62523, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62523, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5320 (p : Pattern) (ha : d62529 p = 1) (hb : d73466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62524 q = 1) (hb : d73461 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62524, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5319 q ha hb
    | true =>
      simp only [d62524, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62525 q = 1) (hb : d73462 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62525, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62525, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62526 q = 1) (hb : d73463 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62526, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62526, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62527 q = 1) (hb : d73464 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62527, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62527, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62528 q = 1) (hb : d73465 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62528, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62528, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62529 q = 1) (hb : d73466 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62529, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62529, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5321 (p : Pattern) (ha : d62535 p = 1) (hb : d73472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62530 q = 1) (hb : d73467 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62530, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5320 q ha hb
    | true =>
      simp only [d62530, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62531 q = 1) (hb : d73468 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62531, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62531, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62532 q = 1) (hb : d73469 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62532, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62532, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62533 q = 1) (hb : d73470 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62533, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62533, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62534 q = 1) (hb : d73471 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62534, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62534, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62535 q = 1) (hb : d73472 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62535, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62535, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5322 (p : Pattern) (ha : d62541 p = 1) (hb : d73478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62536 q = 1) (hb : d73473 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62536, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5321 q ha hb
    | true =>
      simp only [d62536, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62537 q = 1) (hb : d73474 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62537, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62537, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62538 q = 1) (hb : d73475 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62538, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62538, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62539 q = 1) (hb : d73476 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62539, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62539, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62540 q = 1) (hb : d73477 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62540, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62540, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62541 q = 1) (hb : d73478 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62541, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62541, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5323 (p : Pattern) (ha : d62547 p = 1) (hb : d73484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62542 q = 1) (hb : d73479 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62542, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5322 q ha hb
    | true =>
      simp only [d62542, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62543 q = 1) (hb : d73480 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62543, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62543, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62544 q = 1) (hb : d73481 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62544, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62544, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62545 q = 1) (hb : d73482 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62545, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62545, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62546 q = 1) (hb : d73483 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62546, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62546, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62547 q = 1) (hb : d73484 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62547, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62547, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5324 (p : Pattern) (ha : d62553 p = 1) (hb : d73490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62548 q = 1) (hb : d73485 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62548, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5323 q ha hb
    | true =>
      simp only [d62548, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62549 q = 1) (hb : d73486 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62549, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62549, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62550 q = 1) (hb : d73487 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62550, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62550, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62551 q = 1) (hb : d73488 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62551, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62551, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62552 q = 1) (hb : d73489 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62552, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62552, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62553 q = 1) (hb : d73490 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62553, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62553, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5325 (p : Pattern) (ha : d61683 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d3329, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3330 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61680 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61681 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61682 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61683 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5326 (p : Pattern) (ha : d61692 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d3343, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3344 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61689 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61690 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61691 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61692 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5327 (p : Pattern) (ha : d61698 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61684 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5325 q ha hb
  have h2 (q : Pattern) (ha : d61685 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61686 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61687 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61688 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61693 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5326 q ha hb
  have h7 (q : Pattern) (ha : d61694 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61695 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61696 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61697 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61698 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5328 (p : Pattern) (ha : d61702 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d3359, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3360 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61699 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61700 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61701 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61702 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5329 (p : Pattern) (ha : d61708 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61703 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5328 q ha hb
  have h2 (q : Pattern) (ha : d61704 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61705 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61706 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61707 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61708 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5330 (p : Pattern) (ha : d61713 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d3376, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3377 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61710 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61711 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61712 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61713 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5331 (p : Pattern) (ha : d61719 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61714 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5330 q ha hb
  have h2 (q : Pattern) (ha : d61715 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61716 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61717 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61718 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61719 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5332 (p : Pattern) (ha : d61725 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d3394, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3395 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61722 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61723 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61724 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61725 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5333 (p : Pattern) (ha : d61731 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61726 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5332 q ha hb
  have h2 (q : Pattern) (ha : d61727 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61728 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61729 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61730 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61731 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5334 (p : Pattern) (ha : d61738 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d3413, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3414 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61735 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61736 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61737 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61738 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5335 (p : Pattern) (ha : d61744 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61739 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5334 q ha hb
  have h2 (q : Pattern) (ha : d61740 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61741 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61742 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61743 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61744 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5336 (p : Pattern) (ha : d61752 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d3433, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3434 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61749 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61750 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61751 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d61752 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5337 (p : Pattern) (ha : d61758 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61753 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5336 q ha hb
  have h2 (q : Pattern) (ha : d61754 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61755 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61756 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61757 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61758 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5338 (p : Pattern) (ha : d61764 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61709 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5327 q ha hb
    | true =>
      simp only [d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5329 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61720 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5331 q ha hb
  have h3 (q : Pattern) (ha : d61721 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61732 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5333 q ha hb
  have h5 (q : Pattern) (ha : d61733 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61734 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61745 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5335 q ha hb
  have h8 (q : Pattern) (ha : d61746 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61747 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61748 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61759 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5337 q ha hb
  have h12 (q : Pattern) (ha : d61760 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61761 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61762 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61763 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61764 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5339 (p : Pattern) (ha : d61770 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61765 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5338 q ha hb
    | true =>
      simp only [d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61766 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61767 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61768 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61769 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61770 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5340 (p : Pattern) (ha : d61776 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61771 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5339 q ha hb
    | true =>
      simp only [d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61772 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61773 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61774 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61775 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61776 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5341 (p : Pattern) (ha : d61782 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61777 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5340 q ha hb
    | true =>
      simp only [d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61778 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61779 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61780 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61781 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61782 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5342 (p : Pattern) (ha : d61788 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61783 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5341 q ha hb
    | true =>
      simp only [d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61784 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61785 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61786 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61787 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61788 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5343 (p : Pattern) (ha : d61794 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61789 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5342 q ha hb
    | true =>
      simp only [d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61790 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61791 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61792 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61793 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61794 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5344 (p : Pattern) (ha : d61800 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61795 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5343 q ha hb
    | true =>
      simp only [d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61796 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61797 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61798 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61799 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61800 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5345 (p : Pattern) (ha : d61806 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61801 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5344 q ha hb
    | true =>
      simp only [d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d61802 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61803 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61804 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61805 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61806 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5346 (p : Pattern) (ha : d61358 p = 1) (hb : d61544 p = 1) : d72471 p = 1 := by
  have h0 (q : Pattern) (ha : d3331 q = 1) (hb : d61358 q = 1) : d3331 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61539 q = 1) : d61539 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61540 q = 1) : d72467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61540, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61540, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61541 q = 1) : d72468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61541, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61541, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61542 q = 1) : d72469 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61542, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61542, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61543 q = 1) : d72470 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61543, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61543, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61544 q = 1) : d72471 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61544, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61544, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5347 (p : Pattern) (ha : d61358 p = 1) (hb : d61555 p = 1) : d72481 p = 1 := by
  have h0 (q : Pattern) (ha : d3345 q = 1) (hb : d61358 q = 1) : d3345 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61550 q = 1) : d61550 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3347 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61551 q = 1) : d72477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61551, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61551, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61552 q = 1) : d72478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61552, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61552, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61553 q = 1) : d72479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61553, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61553, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61554 q = 1) : d72480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61554, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61554, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61555 q = 1) : d72481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61555, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61555, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5348 (p : Pattern) (ha : d61358 p = 1) (hb : d61561 p = 1) : d72487 p = 1 := by
  have h0 (q : Pattern) (ha : d3328 q = 1) (hb : d61358 q = 1) : d3328 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61545 q = 1) : d72472 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61545, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61545, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5346 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61546 q = 1) : d72473 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61546, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61546, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61547 q = 1) : d72474 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61547, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61547, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61548 q = 1) : d72475 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61548, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61548, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61549 q = 1) : d72476 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61549, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61549, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61556 q = 1) : d72482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61556, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61556, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5347 q ha hb
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61557 q = 1) : d72483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61557, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61557, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61358 q = 1) (hb : d61558 q = 1) : d72484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61558, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61558, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61358 q = 1) (hb : d61559 q = 1) : d72485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61559, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61559, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61358 q = 1) (hb : d61560 q = 1) : d72486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61560, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61560, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61358 q = 1) (hb : d61561 q = 1) : d72487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61561, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61561, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5349 (p : Pattern) (ha : d61358 p = 1) (hb : d61567 p = 1) : d72492 p = 1 := by
  have h0 (q : Pattern) (ha : d3361 q = 1) (hb : d61358 q = 1) : d3361 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61562 q = 1) : d61562 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3363 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61563 q = 1) : d72488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61563, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61563, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61564 q = 1) : d72489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61564, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61564, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61565 q = 1) : d72490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61565, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61565, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61566 q = 1) : d72491 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61566, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61566, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61567 q = 1) : d72492 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61567, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61567, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5350 (p : Pattern) (ha : d61358 p = 1) (hb : d61573 p = 1) : d72498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61568 q = 1) : d72493 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61568, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61568, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5349 q ha hb
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61569 q = 1) : d72494 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61569, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61569, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61570 q = 1) : d72495 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61570, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61570, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61571 q = 1) : d72496 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61571, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61571, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61572 q = 1) : d72497 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61572, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61572, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61573 q = 1) : d72498 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61573, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61573, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5351 (p : Pattern) (ha : d61358 p = 1) (hb : d61580 p = 1) : d72504 p = 1 := by
  have h0 (q : Pattern) (ha : d3378 q = 1) (hb : d61358 q = 1) : d3378 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61575 q = 1) : d61575 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61576 q = 1) : d72500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61576, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61576, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61577 q = 1) : d72501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61577, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61577, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61578 q = 1) : d72502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61578, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61578, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61579 q = 1) : d72503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61579, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61579, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61580 q = 1) : d72504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61580, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61580, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5352 (p : Pattern) (ha : d61358 p = 1) (hb : d61586 p = 1) : d72510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61581 q = 1) : d72505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61581, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61581, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5351 q ha hb
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61582 q = 1) : d72506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61582, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61582, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61583 q = 1) : d72507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61583, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61583, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61584 q = 1) : d72508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61584, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61584, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61585 q = 1) : d72509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61585, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61585, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61586 q = 1) : d72510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61586, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61586, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5353 (p : Pattern) (ha : d61358 p = 1) (hb : d61594 p = 1) : d72517 p = 1 := by
  have h0 (q : Pattern) (ha : d3396 q = 1) (hb : d61358 q = 1) : d3396 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61589 q = 1) : d61589 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61590 q = 1) : d72513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61590, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61590, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61591 q = 1) : d72514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61591, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61591, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61592 q = 1) : d72515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61592, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61592, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61593 q = 1) : d72516 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61593, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61593, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61594 q = 1) : d72517 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61594, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61594, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5354 (p : Pattern) (ha : d61358 p = 1) (hb : d61600 p = 1) : d72523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61595 q = 1) : d72518 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61595, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61595, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5353 q ha hb
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61596 q = 1) : d72519 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61596, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61596, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61597 q = 1) : d72520 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61597, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61597, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61598 q = 1) : d72521 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61598, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61598, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61599 q = 1) : d72522 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61599, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61599, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61600 q = 1) : d72523 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61600, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61600, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5355 (p : Pattern) (ha : d61358 p = 1) (hb : d61609 p = 1) : d72531 p = 1 := by
  have h0 (q : Pattern) (ha : d3415 q = 1) (hb : d61358 q = 1) : d3415 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61604 q = 1) : d61604 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61605 q = 1) : d72527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61605, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61605, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61606 q = 1) : d72528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61606, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61606, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61607 q = 1) : d72529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61607, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61607, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61608 q = 1) : d72530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61608, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61608, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61609 q = 1) : d72531 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61609, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61609, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5356 (p : Pattern) (ha : d61358 p = 1) (hb : d61615 p = 1) : d72537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61610 q = 1) : d72532 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61610, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61610, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5355 q ha hb
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61611 q = 1) : d72533 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61611, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61611, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61612 q = 1) : d72534 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61612, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61612, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61613 q = 1) : d72535 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61613, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61613, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61614 q = 1) : d72536 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61614, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61614, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61615 q = 1) : d72537 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61615, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61615, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5357 (p : Pattern) (ha : d61358 p = 1) (hb : d61625 p = 1) : d72546 p = 1 := by
  have h0 (q : Pattern) (ha : d3435 q = 1) (hb : d61358 q = 1) : d3435 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61357 q = 1) (hb : d61620 q = 1) : d61620 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3437 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61621 q = 1) : d72542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61358, d61621, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61358, d61621, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61622 q = 1) : d72543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61622, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61622, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61623 q = 1) : d72544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61623, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61623, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61624 q = 1) : d72545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61624, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61624, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61625 q = 1) : d72546 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61625, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61625, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro5358 (p : Pattern) (ha : d61358 p = 1) (hb : d61631 p = 1) : d72552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61626 q = 1) : d72547 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61626, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61626, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5357 q ha hb
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61627 q = 1) : d72548 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61627, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61627, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61628 q = 1) : d72549 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61628, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61628, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61629 q = 1) : d72550 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61629, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61629, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61630 q = 1) : d72551 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61630, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61630, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61631 q = 1) : d72552 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61631, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61631, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5359 (p : Pattern) (ha : d61358 p = 1) (hb : d61637 p = 1) : d72558 p = 1 := by
  have h0 (q : Pattern) (ha : d61358 q = 1) (hb : d61574 q = 1) : d72499 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61574, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5348 q ha hb
    | true =>
      simp only [d61574, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5350 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61587 q = 1) : d72511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61587, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61587, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5352 q ha hb
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61588 q = 1) : d72512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61588, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61588, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61601 q = 1) : d72524 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61601, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61601, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5354 q ha hb
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61602 q = 1) : d72525 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61602, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61602, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61603 q = 1) : d72526 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61603, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61603, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61358 q = 1) (hb : d61616 q = 1) : d72538 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61616, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61616, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5356 q ha hb
  have h8 (q : Pattern) (ha : d61358 q = 1) (hb : d61617 q = 1) : d72539 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61617, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61617, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61358 q = 1) (hb : d61618 q = 1) : d72540 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61618, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61618, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61358 q = 1) (hb : d61619 q = 1) : d72541 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61619, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61619, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61358 q = 1) (hb : d61632 q = 1) : d72553 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61632, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61632, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5358 q ha hb
  have h12 (q : Pattern) (ha : d61358 q = 1) (hb : d61633 q = 1) : d72554 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61633, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61633, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61358 q = 1) (hb : d61634 q = 1) : d72555 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61634, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61634, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61358 q = 1) (hb : d61635 q = 1) : d72556 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61635, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61635, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61358 q = 1) (hb : d61636 q = 1) : d72557 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61636, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61636, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61358 q = 1) (hb : d61637 q = 1) : d72558 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61637, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61637, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5360 (p : Pattern) (ha : d61358 p = 1) (hb : d61643 p = 1) : d72564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61638 q = 1) : d72559 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61638, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5359 q ha hb
    | true =>
      simp only [d61638, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61639 q = 1) : d72560 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61639, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61639, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61640 q = 1) : d72561 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61640, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61640, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61641 q = 1) : d72562 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61641, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61641, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61642 q = 1) : d72563 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61642, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61642, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61643 q = 1) : d72564 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61643, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61643, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5361 (p : Pattern) (ha : d61358 p = 1) (hb : d61649 p = 1) : d72570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61644 q = 1) : d72565 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61644, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5360 q ha hb
    | true =>
      simp only [d61644, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61645 q = 1) : d72566 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61645, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61645, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61646 q = 1) : d72567 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61646, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61646, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61647 q = 1) : d72568 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61647, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61647, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61648 q = 1) : d72569 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61648, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61648, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61649 q = 1) : d72570 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61649, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61649, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5362 (p : Pattern) (ha : d61358 p = 1) (hb : d61655 p = 1) : d72576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61650 q = 1) : d72571 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61650, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5361 q ha hb
    | true =>
      simp only [d61650, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61651 q = 1) : d72572 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61651, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61651, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61652 q = 1) : d72573 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61652, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61652, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61653 q = 1) : d72574 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61653, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61653, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61654 q = 1) : d72575 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61654, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61654, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61655 q = 1) : d72576 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61655, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61655, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5363 (p : Pattern) (ha : d61358 p = 1) (hb : d61661 p = 1) : d72582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61656 q = 1) : d72577 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61656, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5362 q ha hb
    | true =>
      simp only [d61656, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61657 q = 1) : d72578 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61657, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61657, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61658 q = 1) : d72579 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61658, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61658, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61659 q = 1) : d72580 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61659, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61659, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61660 q = 1) : d72581 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61660, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61660, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61661 q = 1) : d72582 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61661, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61661, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5364 (p : Pattern) (ha : d61358 p = 1) (hb : d61667 p = 1) : d72588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61662 q = 1) : d72583 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61662, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5363 q ha hb
    | true =>
      simp only [d61662, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61663 q = 1) : d72584 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61663, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61663, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61664 q = 1) : d72585 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61664, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61664, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61665 q = 1) : d72586 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61665, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61665, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61666 q = 1) : d72587 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61666, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61666, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61667 q = 1) : d72588 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61667, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61667, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5365 (p : Pattern) (ha : d61358 p = 1) (hb : d61673 p = 1) : d72594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61668 q = 1) : d72589 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61668, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5364 q ha hb
    | true =>
      simp only [d61668, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61669 q = 1) : d72590 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61669, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61669, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61670 q = 1) : d72591 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61670, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61670, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61671 q = 1) : d72592 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61671, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61671, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61672 q = 1) : d72593 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61672, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61672, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61673 q = 1) : d72594 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61673, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61673, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5366 (p : Pattern) (ha : d61358 p = 1) (hb : d61679 p = 1) : d72600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61358 q = 1) (hb : d61674 q = 1) : d72595 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61674, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5365 q ha hb
    | true =>
      simp only [d61674, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61358 q = 1) (hb : d61675 q = 1) : d72596 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61675, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61675, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61358 q = 1) (hb : d61676 q = 1) : d72597 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61676, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61676, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61358 q = 1) (hb : d61677 q = 1) : d72598 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61677, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61677, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61358 q = 1) (hb : d61678 q = 1) : d72599 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61678, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61678, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61358 q = 1) (hb : d61679 q = 1) : d72600 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61679, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61679, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5367 (p : Pattern) (ha : d3324 p = 1) (hb : d51947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51907 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3319 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6 q ha hb
    | true =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3320 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3321 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3322 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51916 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3323 q = 1) (hb : d51917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3323, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51946 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3324 q = 1) (hb : d51947 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, d51947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3324, d51947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5368 (p : Pattern) (ha : d58438 p = 1) (hb : d72471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3331 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58434 q = 1) (hb : d72467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58434, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58434, d72467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58435 q = 1) (hb : d72468 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58435, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58435, d72468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58436 q = 1) (hb : d72469 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58436, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58436, d72469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58437 q = 1) (hb : d72470 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58437, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58437, d72470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58438 q = 1) (hb : d72471 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58438, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58438, d72471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5369 (p : Pattern) (ha : d58455 p = 1) (hb : d72481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3345 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58444 q = 1) (hb : d72477 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58444, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58444, d72477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58445 q = 1) (hb : d72478 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58445, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58445, d72478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58446 q = 1) (hb : d72479 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58446, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58446, d72479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58449 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58450 q = 1) (hb : d72480 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58450, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58450, d72480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58454 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58455 q = 1) (hb : d72481 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58455, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58455, d72481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5370 (p : Pattern) (ha : d58461 p = 1) (hb : d72487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5367 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58439 q = 1) (hb : d72472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58439, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58439, d72472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5368 q ha hb
  have h6 (q : Pattern) (ha : d58440 q = 1) (hb : d72473 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58440, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58440, d72473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58441 q = 1) (hb : d72474 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58441, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58441, d72474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58442 q = 1) (hb : d72475 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58442, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58442, d72475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58443 q = 1) (hb : d72476 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58443, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58443, d72476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58456 q = 1) (hb : d72482 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58456, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58456, d72482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5369 q ha hb
  have h11 (q : Pattern) (ha : d58457 q = 1) (hb : d72483 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58457, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58457, d72483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58458 q = 1) (hb : d72484 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58458, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58458, d72484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58459 q = 1) (hb : d72485 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58459, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58459, d72485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58460 q = 1) (hb : d72486 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58460, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58460, d72486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58461 q = 1) (hb : d72487 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58461, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58461, d72487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5371 (p : Pattern) (ha : d58473 p = 1) (hb : d72492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3361 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58462 q = 1) (hb : d72488 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58462, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58462, d72488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58463 q = 1) (hb : d72489 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58463, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58463, d72489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58464 q = 1) (hb : d72490 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58464, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58464, d72490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58467 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58468 q = 1) (hb : d72491 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58468, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58468, d72491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58472 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58473 q = 1) (hb : d72492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58473, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58473, d72492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5372 (p : Pattern) (ha : d58479 p = 1) (hb : d72498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58474 q = 1) (hb : d72493 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58474, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58474, d72493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5371 q ha hb
  have h2 (q : Pattern) (ha : d58475 q = 1) (hb : d72494 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58475, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58475, d72494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58476 q = 1) (hb : d72495 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58476, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58476, d72495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58477 q = 1) (hb : d72496 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58477, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58477, d72496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58478 q = 1) (hb : d72497 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58478, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58478, d72497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58479 q = 1) (hb : d72498 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58479, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58479, d72498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5373 (p : Pattern) (ha : d58492 p = 1) (hb : d72504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3378 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58481 q = 1) (hb : d72500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58481, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58481, d72500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58482 q = 1) (hb : d72501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58482, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58482, d72501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58483 q = 1) (hb : d72502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58483, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58483, d72502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58486 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58487 q = 1) (hb : d72503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58487, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58487, d72503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58491 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58492 q = 1) (hb : d72504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58492, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58492, d72504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5374 (p : Pattern) (ha : d58498 p = 1) (hb : d72510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58493 q = 1) (hb : d72505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58493, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58493, d72505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5373 q ha hb
  have h2 (q : Pattern) (ha : d58494 q = 1) (hb : d72506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58494, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58494, d72506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58495 q = 1) (hb : d72507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58495, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58495, d72507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58496 q = 1) (hb : d72508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58496, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58496, d72508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58497 q = 1) (hb : d72509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58497, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58497, d72509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58498 q = 1) (hb : d72510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58498, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58498, d72510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5375 (p : Pattern) (ha : d58512 p = 1) (hb : d72517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3396 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58501 q = 1) (hb : d72513 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58501, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58501, d72513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58502 q = 1) (hb : d72514 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58502, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58502, d72514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58503 q = 1) (hb : d72515 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58503, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58503, d72515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58506 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58507 q = 1) (hb : d72516 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58507, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58507, d72516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58511 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58512 q = 1) (hb : d72517 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58512, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58512, d72517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5376 (p : Pattern) (ha : d58518 p = 1) (hb : d72523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58513 q = 1) (hb : d72518 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58513, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58513, d72518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5375 q ha hb
  have h2 (q : Pattern) (ha : d58514 q = 1) (hb : d72519 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58514, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58514, d72519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58515 q = 1) (hb : d72520 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58515, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58515, d72520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58516 q = 1) (hb : d72521 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58516, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58516, d72521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58517 q = 1) (hb : d72522 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58517, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58517, d72522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58518 q = 1) (hb : d72523 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58518, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58518, d72523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5377 (p : Pattern) (ha : d58533 p = 1) (hb : d72531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3415 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58522 q = 1) (hb : d72527 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58522, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58522, d72527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58523 q = 1) (hb : d72528 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58523, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58523, d72528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58524 q = 1) (hb : d72529 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58524, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58524, d72529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58527 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58528 q = 1) (hb : d72530 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58528, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58528, d72530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58532 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58533 q = 1) (hb : d72531 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58533, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58533, d72531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5378 (p : Pattern) (ha : d58539 p = 1) (hb : d72537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58534 q = 1) (hb : d72532 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58534, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58534, d72532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5377 q ha hb
  have h2 (q : Pattern) (ha : d58535 q = 1) (hb : d72533 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58535, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58535, d72533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58536 q = 1) (hb : d72534 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58536, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58536, d72534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58537 q = 1) (hb : d72535 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58537, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58537, d72535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58538 q = 1) (hb : d72536 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58538, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58538, d72536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58539 q = 1) (hb : d72537 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58539, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58539, d72537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5379 (p : Pattern) (ha : d58555 p = 1) (hb : d72546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3435 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d58544 q = 1) (hb : d72542 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58544, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58544, d72542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d58545 q = 1) (hb : d72543 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58545, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58545, d72543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h10 (q : Pattern) (ha : d58546 q = 1) (hb : d72544 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58546, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d58546, d72544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d58549 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d58550 q = 1) (hb : d72545 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58550, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58550, d72545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d58554 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d58555 q = 1) (hb : d72546 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58555, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58555, d72546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro5380 (p : Pattern) (ha : d58561 p = 1) (hb : d72552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58556 q = 1) (hb : d72547 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58556, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58556, d72547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5379 q ha hb
  have h2 (q : Pattern) (ha : d58557 q = 1) (hb : d72548 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58557, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58557, d72548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58558 q = 1) (hb : d72549 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58558, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58558, d72549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58559 q = 1) (hb : d72550 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58559, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58559, d72550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58560 q = 1) (hb : d72551 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58560, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58560, d72551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58561 q = 1) (hb : d72552 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58561, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58561, d72552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5381 (p : Pattern) (ha : d58567 p = 1) (hb : d72558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d58480 q = 1) (hb : d72499 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58480, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5370 q ha hb
    | true =>
      simp only [d58480, d72499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5372 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58499 q = 1) (hb : d72511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58499, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58499, d72511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5374 q ha hb
  have h3 (q : Pattern) (ha : d58500 q = 1) (hb : d72512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58500, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58500, d72512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58519 q = 1) (hb : d72524 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58519, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58519, d72524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5376 q ha hb
  have h5 (q : Pattern) (ha : d58520 q = 1) (hb : d72525 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58520, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58520, d72525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58521 q = 1) (hb : d72526 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58521, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58521, d72526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58540 q = 1) (hb : d72538 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58540, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58540, d72538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5378 q ha hb
  have h8 (q : Pattern) (ha : d58541 q = 1) (hb : d72539 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58541, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58541, d72539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58542 q = 1) (hb : d72540 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58542, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58542, d72540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58543 q = 1) (hb : d72541 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58543, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58543, d72541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58562 q = 1) (hb : d72553 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58562, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58562, d72553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5380 q ha hb
  have h12 (q : Pattern) (ha : d58563 q = 1) (hb : d72554 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58563, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58563, d72554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58564 q = 1) (hb : d72555 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58564, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58564, d72555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58565 q = 1) (hb : d72556 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58565, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58565, d72556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58566 q = 1) (hb : d72557 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58566, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58566, d72557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58567 q = 1) (hb : d72558 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58567, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58567, d72558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5382 (p : Pattern) (ha : d58573 p = 1) (hb : d72564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58568 q = 1) (hb : d72559 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58568, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5381 q ha hb
    | true =>
      simp only [d58568, d72559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58569 q = 1) (hb : d72560 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58569, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58569, d72560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58570 q = 1) (hb : d72561 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58570, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58570, d72561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58571 q = 1) (hb : d72562 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58571, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58571, d72562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58572 q = 1) (hb : d72563 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58572, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58572, d72563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58573 q = 1) (hb : d72564 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58573, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58573, d72564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5383 (p : Pattern) (ha : d58579 p = 1) (hb : d72570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58574 q = 1) (hb : d72565 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58574, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5382 q ha hb
    | true =>
      simp only [d58574, d72565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58575 q = 1) (hb : d72566 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58575, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58575, d72566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58576 q = 1) (hb : d72567 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58576, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58576, d72567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58577 q = 1) (hb : d72568 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58577, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58577, d72568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58578 q = 1) (hb : d72569 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58578, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58578, d72569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58579 q = 1) (hb : d72570 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58579, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58579, d72570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5384 (p : Pattern) (ha : d58585 p = 1) (hb : d72576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58580 q = 1) (hb : d72571 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58580, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5383 q ha hb
    | true =>
      simp only [d58580, d72571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58581 q = 1) (hb : d72572 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58581, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58581, d72572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58582 q = 1) (hb : d72573 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58582, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58582, d72573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58583 q = 1) (hb : d72574 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58583, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58583, d72574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58584 q = 1) (hb : d72575 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58584, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58584, d72575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58585 q = 1) (hb : d72576 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58585, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58585, d72576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5385 (p : Pattern) (ha : d58591 p = 1) (hb : d72582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58586 q = 1) (hb : d72577 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58586, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5384 q ha hb
    | true =>
      simp only [d58586, d72577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58587 q = 1) (hb : d72578 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58587, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58587, d72578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58588 q = 1) (hb : d72579 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58588, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58588, d72579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58589 q = 1) (hb : d72580 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58589, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58589, d72580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58590 q = 1) (hb : d72581 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58590, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58590, d72581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58591 q = 1) (hb : d72582 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58591, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58591, d72582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5386 (p : Pattern) (ha : d58597 p = 1) (hb : d72588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58592 q = 1) (hb : d72583 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58592, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5385 q ha hb
    | true =>
      simp only [d58592, d72583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58593 q = 1) (hb : d72584 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58593, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58593, d72584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58594 q = 1) (hb : d72585 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58594, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58594, d72585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58595 q = 1) (hb : d72586 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58595, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58595, d72586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58596 q = 1) (hb : d72587 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58596, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58596, d72587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58597 q = 1) (hb : d72588 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58597, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58597, d72588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5387 (p : Pattern) (ha : d58603 p = 1) (hb : d72594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58598 q = 1) (hb : d72589 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58598, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5386 q ha hb
    | true =>
      simp only [d58598, d72589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58599 q = 1) (hb : d72590 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58599, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58599, d72590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58600 q = 1) (hb : d72591 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58600, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58600, d72591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58601 q = 1) (hb : d72592 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58601, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58601, d72592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58602 q = 1) (hb : d72593 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58602, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58602, d72593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58603 q = 1) (hb : d72594 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58603, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58603, d72594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5388 (p : Pattern) (ha : d58609 p = 1) (hb : d72600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58604 q = 1) (hb : d72595 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58604, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5387 q ha hb
    | true =>
      simp only [d58604, d72595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58605 q = 1) (hb : d72596 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58605, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58605, d72596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58606 q = 1) (hb : d72597 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58606, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58606, d72597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58607 q = 1) (hb : d72598 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58607, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58607, d72598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58608 q = 1) (hb : d72599 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58608, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58608, d72599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58609 q = 1) (hb : d72600 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58609, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58609, d72600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5389 (p : Pattern) (ha : d61358 p = 1) (hb : d61806 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d61358 q = 1) (hb : d61806 q = 1) : d61806 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro5390 (p : Pattern) (ha : d58438 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d58434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d58434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d58434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58435 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58435, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58435, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58436 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58436, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58436, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58437 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58437, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58437, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58438 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58438, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58438, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5391 (p : Pattern) (ha : d58455 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d58444 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d58444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d58444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58445 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58445, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58445, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58446 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58446, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58446, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58449 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58450 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58450, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58450, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58455 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58455, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58455, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5392 (p : Pattern) (ha : d58461 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58439 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58439, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58439, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5390 q ha hb
  have h3 (q : Pattern) (ha : d58440 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58440, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58440, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58441 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58441, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58441, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58442 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58442, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58442, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58443 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58443, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58443, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58456 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58456, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58456, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5391 q ha hb
  have h8 (q : Pattern) (ha : d58457 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58457, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58457, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58458 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58458, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58458, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58459 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58459, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58459, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58460 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58460, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58460, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58461 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58461, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58461, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5393 (p : Pattern) (ha : d58473 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d58462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d58462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d58462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58463 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58463, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58463, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58464 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58464, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58464, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58467 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58468 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58468, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58468, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58472 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58473 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58473, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58473, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5394 (p : Pattern) (ha : d58479 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58474 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58474, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58474, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5393 q ha hb
  have h2 (q : Pattern) (ha : d58475 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58475, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58475, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58476 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58476, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58476, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58477 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58477, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58477, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58478 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58478, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58478, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58479 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58479, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58479, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5395 (p : Pattern) (ha : d58492 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d58481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d58481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d58481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58482 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58482, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58482, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58483 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58483, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58483, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58486 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58487 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58487, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58487, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58491 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58492 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58492, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58492, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5396 (p : Pattern) (ha : d58498 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58493 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58493, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58493, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5395 q ha hb
  have h2 (q : Pattern) (ha : d58494 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58494, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58494, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58495 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58495, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58495, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58496 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58496, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58496, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58497 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58497, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58497, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58498 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58498, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58498, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5397 (p : Pattern) (ha : d58512 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d58501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d58501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d58501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58502 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58502, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58502, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58503 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58503, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58503, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58506 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58507 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58507, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58507, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58511 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58512 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58512, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58512, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5398 (p : Pattern) (ha : d58518 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58513 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58513, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58513, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5397 q ha hb
  have h2 (q : Pattern) (ha : d58514 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58514, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58514, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58515 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58515, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58515, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58516 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58516, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58516, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58517 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58517, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58517, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58518 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58518, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58518, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5399 (p : Pattern) (ha : d58533 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d58522 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d58522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d58522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58523 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58523, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58523, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58524 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58524, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58524, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58527 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58528 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58528, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58528, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58532 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58533 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58533, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58533, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5400 (p : Pattern) (ha : d58539 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58534 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58534, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58534, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5399 q ha hb
  have h2 (q : Pattern) (ha : d58535 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58535, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58535, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58536 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58536, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58536, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58537 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58537, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58537, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58538 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58538, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58538, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58539 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58539, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58539, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5401 (p : Pattern) (ha : d58555 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d58544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d58544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d58544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58545 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58545, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58545, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d58546 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58546, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58546, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58549 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58550 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58550, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58550, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d58554 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58555 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58555, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58555, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5402 (p : Pattern) (ha : d58561 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58556 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58556, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58556, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5401 q ha hb
  have h2 (q : Pattern) (ha : d58557 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58557, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58557, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58558 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58558, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58558, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58559 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58559, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58559, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58560 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58560, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58560, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58561 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58561, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58561, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5403 (p : Pattern) (ha : d58567 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d58480 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58480, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5392 q ha hb
    | true =>
      simp only [d58480, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5394 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58499 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58499, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58499, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5396 q ha hb
  have h3 (q : Pattern) (ha : d58500 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58500, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58500, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58519 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58519, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58519, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5398 q ha hb
  have h5 (q : Pattern) (ha : d58520 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58520, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58520, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58521 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58521, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58521, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58540 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58540, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58540, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5400 q ha hb
  have h8 (q : Pattern) (ha : d58541 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58541, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58541, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58542 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58542, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58542, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58543 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58543, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58543, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58562 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58562, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58562, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5402 q ha hb
  have h12 (q : Pattern) (ha : d58563 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58563, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58563, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58564 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58564, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58564, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58565 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58565, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d58565, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58566 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58566, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58566, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58567 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58567, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58567, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5404 (p : Pattern) (ha : d58573 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58568 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58568, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5403 q ha hb
    | true =>
      simp only [d58568, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58569 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58569, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58569, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58570 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58570, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58570, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58571 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58571, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58571, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58572 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58572, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58572, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58573 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58573, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58573, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5405 (p : Pattern) (ha : d58579 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58574 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58574, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5404 q ha hb
    | true =>
      simp only [d58574, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58575 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58575, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58575, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58576 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58576, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58576, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58577 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58577, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58577, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58578 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58578, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58578, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58579 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58579, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58579, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5406 (p : Pattern) (ha : d58585 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58580 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58580, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5405 q ha hb
    | true =>
      simp only [d58580, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58581 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58581, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58581, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58582 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58582, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58582, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58583 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58583, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58583, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58584 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58584, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58584, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58585 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58585, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58585, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5407 (p : Pattern) (ha : d58591 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58586 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58586, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5406 q ha hb
    | true =>
      simp only [d58586, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58587 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58587, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58587, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58588 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58588, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58588, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58589 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58589, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58589, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58590 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58590, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58590, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58591 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58591, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58591, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5408 (p : Pattern) (ha : d58597 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58592 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58592, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5407 q ha hb
    | true =>
      simp only [d58592, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58593 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58593, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58593, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58594 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58594, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58594, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58595 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58595, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58595, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58596 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58596, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58596, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58597 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58597, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58597, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5409 (p : Pattern) (ha : d58603 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58598 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58598, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5408 q ha hb
    | true =>
      simp only [d58598, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58599 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58599, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58599, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58600 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58600, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58600, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58601 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58601, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58601, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58602 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58602, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58602, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58603 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58603, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58603, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5410 (p : Pattern) (ha : d58609 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58604 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58604, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5409 q ha hb
    | true =>
      simp only [d58604, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d58605 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58605, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58605, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d58606 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58606, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58606, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d58607 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58607, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58607, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d58608 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58608, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58608, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d58609 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58609, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58609, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5411 (p : Pattern) (ha : d58614 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d58610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58611 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58611, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58611, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58612 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58612, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58612, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4353 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58613 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58613, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58613, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4364 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58614 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58614, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5412 (p : Pattern) (ha : d58624 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d58620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58621 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58621, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58621, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58622 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58622, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58622, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4389 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58623 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58623, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58623, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4400 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58624 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58624, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5413 (p : Pattern) (ha : d58630 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58615 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58615, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5411 q ha hb
  have h3 (q : Pattern) (ha : d58616 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58616, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58617 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58617, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58618 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58618, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58619 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58619, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58625 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58625, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5412 q ha hb
  have h8 (q : Pattern) (ha : d58626 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58626, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58627 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58627, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58628 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58628, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58629 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58629, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58630 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58630, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5414 (p : Pattern) (ha : d58635 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d58631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58632 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58632, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58632, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58633 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58633, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58633, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4426 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58634 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58634, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58634, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4437 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58635 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58635, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5415 (p : Pattern) (ha : d58641 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5414 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5416 (p : Pattern) (ha : d58647 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d58643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58644 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58644, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58644, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58645 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58645, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58645, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4464 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58646 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58646, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58646, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4475 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58647 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58647, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5417 (p : Pattern) (ha : d58653 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5416 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5418 (p : Pattern) (ha : d58660 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d58656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58657 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58657, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58658 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58658, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4503 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58659 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58659, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4514 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58660 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58660, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5419 (p : Pattern) (ha : d58666 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5418 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5420 (p : Pattern) (ha : d58674 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d58670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58671 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58671, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58672 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58672, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4543 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58673 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58673, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4554 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58674 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58674, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5421 (p : Pattern) (ha : d58680 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5420 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5422 (p : Pattern) (ha : d58689 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d58685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58686 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58686, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d58686, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d58687 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58687, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58687, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4584 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58688 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58688, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58688, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d4595 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58689 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58689, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro5423 (p : Pattern) (ha : d58695 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5422 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5424 (p : Pattern) (ha : d58701 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5413 q ha hb
    | true =>
      simp only [d58642, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5415 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5417 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5419 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5421 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5423 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5425 (p : Pattern) (ha : d58707 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5424 q ha hb
    | true =>
      simp only [d58702, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5426 (p : Pattern) (ha : d58713 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5425 q ha hb
    | true =>
      simp only [d58708, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5427 (p : Pattern) (ha : d58719 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5426 q ha hb
    | true =>
      simp only [d58714, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5428 (p : Pattern) (ha : d58725 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5427 q ha hb
    | true =>
      simp only [d58720, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5429 (p : Pattern) (ha : d58731 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5428 q ha hb
    | true =>
      simp only [d58726, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5430 (p : Pattern) (ha : d58737 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5429 q ha hb
    | true =>
      simp only [d58732, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58736 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58737 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58737, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5431 (p : Pattern) (ha : d58743 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5430 q ha hb
    | true =>
      simp only [d58738, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5432 (p : Pattern) (ha : d61679 p = 1) (hb : d64542 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (ha : d61679 q = 1) (hb : d64542 q = 1) : d61679 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5433 (p : Pattern) (ha : d3324 p = 1) (hb : d54633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51907 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3319 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6 q ha hb
    | true =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3320 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3321 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3322 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3323 q = 1) (hb : d54632 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, d54632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3323, d54632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d3324 q = 1) (hb : d54633 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, d54633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3324, d54633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro5434 (p : Pattern) (ha : d54639 p = 1) (hb : d61544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3331 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d52033 q = 1) (hb : d61540 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52034 q = 1) (hb : d61541 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52035 q = 1) (hb : d61542 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54638 q = 1) (hb : d61543 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54638, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54638, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54639 q = 1) (hb : d61544 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54639, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54639, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5435 (p : Pattern) (ha : d54646 p = 1) (hb : d61555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3345 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3347 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52165 q = 1) (hb : d61551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52166 q = 1) (hb : d61552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52167 q = 1) (hb : d61553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54645 q = 1) (hb : d61554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54645, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54645, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54646 q = 1) (hb : d61555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54646, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54646, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5436 (p : Pattern) (ha : d54652 p = 1) (hb : d61561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d54634 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5433 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d54635 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d54636 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54640 q = 1) (hb : d61545 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54640, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54640, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5434 q ha hb
  have h6 (q : Pattern) (ha : d54641 q = 1) (hb : d61546 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54641, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54641, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54642 q = 1) (hb : d61547 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54642, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54642, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54643 q = 1) (hb : d61548 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54643, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54643, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54644 q = 1) (hb : d61549 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54644, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54644, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54647 q = 1) (hb : d61556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54647, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54647, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5435 q ha hb
  have h11 (q : Pattern) (ha : d54648 q = 1) (hb : d61557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54648, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54648, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54649 q = 1) (hb : d61558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54649, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54649, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54650 q = 1) (hb : d61559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54650, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54650, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54651 q = 1) (hb : d61560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54651, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54651, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54652 q = 1) (hb : d61561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54652, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54652, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5437 (p : Pattern) (ha : d54654 p = 1) (hb : d61567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3361 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3363 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52350 q = 1) (hb : d61563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52351 q = 1) (hb : d61564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52352 q = 1) (hb : d61565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54653 q = 1) (hb : d61566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54653, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54653, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54654 q = 1) (hb : d61567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54654, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54654, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5438 (p : Pattern) (ha : d54660 p = 1) (hb : d61573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54655 q = 1) (hb : d61568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54655, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54655, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5437 q ha hb
  have h2 (q : Pattern) (ha : d54656 q = 1) (hb : d61569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54656, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54656, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54657 q = 1) (hb : d61570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54657, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54657, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54658 q = 1) (hb : d61571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54658, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54658, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54659 q = 1) (hb : d61572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54659, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54659, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54660 q = 1) (hb : d61573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54660, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54660, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5439 (p : Pattern) (ha : d54663 p = 1) (hb : d61580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3378 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3380 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52571 q = 1) (hb : d61576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52572 q = 1) (hb : d61577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52573 q = 1) (hb : d61578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54662 q = 1) (hb : d61579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54662, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54662, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54663 q = 1) (hb : d61580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54663, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54663, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5440 (p : Pattern) (ha : d54669 p = 1) (hb : d61586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54664 q = 1) (hb : d61581 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54664, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54664, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5439 q ha hb
  have h2 (q : Pattern) (ha : d54665 q = 1) (hb : d61582 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54665, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54665, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54666 q = 1) (hb : d61583 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54666, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54666, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54667 q = 1) (hb : d61584 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54667, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54667, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54668 q = 1) (hb : d61585 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54668, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54668, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54669 q = 1) (hb : d61586 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54669, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54669, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5441 (p : Pattern) (ha : d54673 p = 1) (hb : d61594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3396 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3398 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52851 q = 1) (hb : d61590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52852 q = 1) (hb : d61591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52853 q = 1) (hb : d61592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54672 q = 1) (hb : d61593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54672, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54672, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54673 q = 1) (hb : d61594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54673, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54673, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5442 (p : Pattern) (ha : d54679 p = 1) (hb : d61600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54674 q = 1) (hb : d61595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54674, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54674, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5441 q ha hb
  have h2 (q : Pattern) (ha : d54675 q = 1) (hb : d61596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54675, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54675, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54676 q = 1) (hb : d61597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54676, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54676, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54677 q = 1) (hb : d61598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54677, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54677, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54678 q = 1) (hb : d61599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54678, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54678, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54679 q = 1) (hb : d61600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54679, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54679, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5443 (p : Pattern) (ha : d54684 p = 1) (hb : d61609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3415 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3417 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53166 q = 1) (hb : d61605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53167 q = 1) (hb : d61606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53168 q = 1) (hb : d61607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54683 q = 1) (hb : d61608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54683, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54683, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54684 q = 1) (hb : d61609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54684, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54684, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5444 (p : Pattern) (ha : d54690 p = 1) (hb : d61615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54685 q = 1) (hb : d61610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54685, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54685, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5443 q ha hb
  have h2 (q : Pattern) (ha : d54686 q = 1) (hb : d61611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54686, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54686, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54687 q = 1) (hb : d61612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54687, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54687, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54688 q = 1) (hb : d61613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54688, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54688, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54689 q = 1) (hb : d61614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54689, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54689, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54690 q = 1) (hb : d61615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54690, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54690, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5445 (p : Pattern) (ha : d54696 p = 1) (hb : d61625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3435 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3437 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53483 q = 1) (hb : d61621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53484 q = 1) (hb : d61622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53485 q = 1) (hb : d61623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54695 q = 1) (hb : d61624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54695, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54695, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d54696 q = 1) (hb : d61625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54696, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54696, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5446 (p : Pattern) (ha : d54702 p = 1) (hb : d61631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54697 q = 1) (hb : d61626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54697, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54697, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5445 q ha hb
  have h2 (q : Pattern) (ha : d54698 q = 1) (hb : d61627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54698, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54698, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54699 q = 1) (hb : d61628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54699, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54699, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54700 q = 1) (hb : d61629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54700, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54700, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54701 q = 1) (hb : d61630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54701, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54701, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54702 q = 1) (hb : d61631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54702, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54702, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5447 (p : Pattern) (ha : d54708 p = 1) (hb : d61637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54661 q = 1) (hb : d61574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54661, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5436 q ha hb
    | true =>
      simp only [d54661, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5438 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54670 q = 1) (hb : d61587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54670, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54670, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5440 q ha hb
  have h3 (q : Pattern) (ha : d54671 q = 1) (hb : d61588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54671, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54671, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54680 q = 1) (hb : d61601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54680, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54680, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5442 q ha hb
  have h5 (q : Pattern) (ha : d54681 q = 1) (hb : d61602 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54681, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54681, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54682 q = 1) (hb : d61603 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54682, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54682, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54691 q = 1) (hb : d61616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54691, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54691, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5444 q ha hb
  have h8 (q : Pattern) (ha : d54692 q = 1) (hb : d61617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54692, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54692, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54693 q = 1) (hb : d61618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54693, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54693, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54694 q = 1) (hb : d61619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54694, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54694, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54703 q = 1) (hb : d61632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54703, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54703, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5446 q ha hb
  have h12 (q : Pattern) (ha : d54704 q = 1) (hb : d61633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54704, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54704, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54705 q = 1) (hb : d61634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54705, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54705, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54706 q = 1) (hb : d61635 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54706, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54706, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54707 q = 1) (hb : d61636 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54707, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54707, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54708 q = 1) (hb : d61637 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54708, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54708, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5448 (p : Pattern) (ha : d54714 p = 1) (hb : d61643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54709 q = 1) (hb : d61638 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54709, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5447 q ha hb
    | true =>
      simp only [d54709, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54710 q = 1) (hb : d61639 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54710, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54710, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54711 q = 1) (hb : d61640 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54711, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54711, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54712 q = 1) (hb : d61641 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54712, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54712, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54713 q = 1) (hb : d61642 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54713, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54713, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54714 q = 1) (hb : d61643 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54714, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54714, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5449 (p : Pattern) (ha : d54720 p = 1) (hb : d61649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54715 q = 1) (hb : d61644 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54715, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5448 q ha hb
    | true =>
      simp only [d54715, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54716 q = 1) (hb : d61645 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54716, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54716, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54717 q = 1) (hb : d61646 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54717, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54717, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54718 q = 1) (hb : d61647 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54718, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54718, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54719 q = 1) (hb : d61648 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54719, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54719, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54720 q = 1) (hb : d61649 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54720, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54720, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5450 (p : Pattern) (ha : d54726 p = 1) (hb : d61655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54721 q = 1) (hb : d61650 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54721, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5449 q ha hb
    | true =>
      simp only [d54721, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54722 q = 1) (hb : d61651 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54722, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54722, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54723 q = 1) (hb : d61652 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54723, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54723, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54724 q = 1) (hb : d61653 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54724, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54724, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54725 q = 1) (hb : d61654 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54725, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54725, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54726 q = 1) (hb : d61655 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54726, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54726, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5451 (p : Pattern) (ha : d54732 p = 1) (hb : d61661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54727 q = 1) (hb : d61656 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54727, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5450 q ha hb
    | true =>
      simp only [d54727, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54728 q = 1) (hb : d61657 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54728, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54728, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54729 q = 1) (hb : d61658 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54729, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54729, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54730 q = 1) (hb : d61659 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54730, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54730, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54731 q = 1) (hb : d61660 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54731, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54731, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54732 q = 1) (hb : d61661 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54732, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54732, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5452 (p : Pattern) (ha : d54738 p = 1) (hb : d61667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54733 q = 1) (hb : d61662 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54733, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5451 q ha hb
    | true =>
      simp only [d54733, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54734 q = 1) (hb : d61663 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54734, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54734, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54735 q = 1) (hb : d61664 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54735, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54735, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54736 q = 1) (hb : d61665 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54736, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54736, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54737 q = 1) (hb : d61666 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54737, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54737, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54738 q = 1) (hb : d61667 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54738, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54738, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5453 (p : Pattern) (ha : d54744 p = 1) (hb : d61673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54739 q = 1) (hb : d61668 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54739, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5452 q ha hb
    | true =>
      simp only [d54739, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54740 q = 1) (hb : d61669 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54740, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54740, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54741 q = 1) (hb : d61670 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54741, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54741, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54742 q = 1) (hb : d61671 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54742, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54742, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54743 q = 1) (hb : d61672 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54743, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54743, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54744 q = 1) (hb : d61673 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54744, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54744, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5454 (p : Pattern) (ha : d54750 p = 1) (hb : d61679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54745 q = 1) (hb : d61674 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54745, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5453 q ha hb
    | true =>
      simp only [d54745, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54746 q = 1) (hb : d61675 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54746, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54746, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54747 q = 1) (hb : d61676 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54747, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54747, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54748 q = 1) (hb : d61677 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54748, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54748, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54749 q = 1) (hb : d61678 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54749, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54749, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54750 q = 1) (hb : d61679 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54750, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54750, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5455 (p : Pattern) (ha : d61806 p = 1) (hb : d64542 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d61806 q = 1) (hb : d64542 q = 1) : d61806 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5456 (p : Pattern) (ha : d54639 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52034 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52035 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54638 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54638, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54638, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54639 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54639, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54639, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5457 (p : Pattern) (ha : d54646 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52166 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52167 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54645 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54645, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54645, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54646 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54646, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54646, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5458 (p : Pattern) (ha : d54652 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54640 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54640, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54640, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5456 q ha hb
  have h3 (q : Pattern) (ha : d54641 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54641, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54641, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54642 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54642, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54642, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54643 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54643, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54643, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54644 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54644, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54644, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54647 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54647, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54647, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5457 q ha hb
  have h8 (q : Pattern) (ha : d54648 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54648, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54648, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54649 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54649, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54649, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54650 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54650, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54650, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54651 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54651, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54651, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54652 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54652, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54652, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5459 (p : Pattern) (ha : d54654 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52351 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52352 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54653 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54653, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54653, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54654 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54654, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54654, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5460 (p : Pattern) (ha : d54660 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54655 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54655, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54655, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5459 q ha hb
  have h2 (q : Pattern) (ha : d54656 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54656, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54656, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54657 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54657, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54657, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54658 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54658, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54658, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54659 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54659, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54659, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54660 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54660, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54660, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5461 (p : Pattern) (ha : d54663 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52572 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52573 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54662 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54662, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54662, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54663 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54663, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54663, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5462 (p : Pattern) (ha : d54669 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54664 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54664, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54664, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5461 q ha hb
  have h2 (q : Pattern) (ha : d54665 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54665, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54665, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54666 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54666, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54666, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54667 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54667, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54667, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54668 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54668, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54668, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54669 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54669, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54669, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5463 (p : Pattern) (ha : d54673 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52852 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52853 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54672 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54672, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54672, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54673 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54673, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54673, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5464 (p : Pattern) (ha : d54679 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54674 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54674, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54674, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5463 q ha hb
  have h2 (q : Pattern) (ha : d54675 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54675, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54675, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54676 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54676, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54676, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54677 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54677, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54677, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54678 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54678, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54678, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54679 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54679, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54679, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5465 (p : Pattern) (ha : d54684 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53167 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53168 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54683 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54683, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54683, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54684 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54684, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54684, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5466 (p : Pattern) (ha : d54690 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54685 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54685, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54685, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5465 q ha hb
  have h2 (q : Pattern) (ha : d54686 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54686, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54686, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54687 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54687, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54687, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54688 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54688, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54688, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54689 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54689, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54689, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54690 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54690, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54690, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5467 (p : Pattern) (ha : d54696 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro358 q ha hb
    | true =>
      simp only [d3433, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53484 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53484, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53485 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54695 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54695, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54695, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54696 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54696, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54696, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5468 (p : Pattern) (ha : d54702 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54697 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54697, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54697, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5467 q ha hb
  have h2 (q : Pattern) (ha : d54698 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54698, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54698, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54699 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54699, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54699, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54700 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54700, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54700, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54701 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54701, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54701, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54702 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54702, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54702, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5469 (p : Pattern) (ha : d54708 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54661 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54661, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5458 q ha hb
    | true =>
      simp only [d54661, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5460 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54670 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54670, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54670, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5462 q ha hb
  have h3 (q : Pattern) (ha : d54671 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54671, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54671, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54680 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54680, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54680, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5464 q ha hb
  have h5 (q : Pattern) (ha : d54681 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54681, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54681, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54682 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54682, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54682, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54691 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54691, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54691, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5466 q ha hb
  have h8 (q : Pattern) (ha : d54692 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54692, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54692, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54693 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54693, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54693, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54694 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54694, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54694, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54703 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54703, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54703, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5468 q ha hb
  have h12 (q : Pattern) (ha : d54704 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54704, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54704, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54705 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54705, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54705, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54706 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54706, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54706, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54707 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54707, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54707, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54708 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54708, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54708, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5470 (p : Pattern) (ha : d54714 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54709 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54709, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5469 q ha hb
    | true =>
      simp only [d54709, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54710 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54710, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54710, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54711 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54711, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54711, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54712 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54712, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54712, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54713 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54713, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54713, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54714 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54714, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54714, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5471 (p : Pattern) (ha : d54720 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54715 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54715, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5470 q ha hb
    | true =>
      simp only [d54715, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54716 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54716, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54716, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54717 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54717, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54717, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54718 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54718, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54718, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54719 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54719, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54719, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54720 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54720, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54720, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5472 (p : Pattern) (ha : d54726 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54721 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54721, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5471 q ha hb
    | true =>
      simp only [d54721, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54722 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54722, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54722, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54723 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54723, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54723, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54724 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54724, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54724, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54725 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54725, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54725, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54726 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54726, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54726, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5473 (p : Pattern) (ha : d54732 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54727 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54727, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5472 q ha hb
    | true =>
      simp only [d54727, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54728 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54728, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54728, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54729 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54729, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54729, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54730 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54730, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54730, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54731 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54731, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54731, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54732 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54732, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54732, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5474 (p : Pattern) (ha : d54738 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54733 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54733, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5473 q ha hb
    | true =>
      simp only [d54733, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54734 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54734, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54734, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54735 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54735, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54735, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54736 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54736, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54736, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54737 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54737, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54737, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54738 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54738, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54738, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5475 (p : Pattern) (ha : d54744 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54739 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54739, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5474 q ha hb
    | true =>
      simp only [d54739, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54740 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54740, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54740, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54741 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54741, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54741, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54742 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54742, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54742, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54743 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54743, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54743, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54744 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54744, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54744, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5476 (p : Pattern) (ha : d54750 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54745 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54745, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5475 q ha hb
    | true =>
      simp only [d54745, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54746 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54746, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54746, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54747 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54747, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54747, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54748 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54748, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54748, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54749 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54749, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54749, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54750 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54750, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54750, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5477 (p : Pattern) (ha : d54752 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro372 q ha hb
    | true =>
      simp only [d3329, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51649 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51649, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51650 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54751 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54751, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54751, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54752 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54752, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54752, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5478 (p : Pattern) (ha : d54759 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro377 q ha hb
    | true =>
      simp only [d3343, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51666 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51666, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51667 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54758 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54758, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54758, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54759 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54759, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54759, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5479 (p : Pattern) (ha : d54765 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54753 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54753, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54753, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5477 q ha hb
  have h3 (q : Pattern) (ha : d54754 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54754, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54754, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54755 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54755, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54755, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54756 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54756, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54756, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54757 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54757, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54757, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54760 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54760, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54760, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5478 q ha hb
  have h8 (q : Pattern) (ha : d54761 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54761, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54761, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54762 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54762, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54762, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54763 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54763, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54763, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54764 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54764, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54764, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54765 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54765, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54765, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5480 (p : Pattern) (ha : d54767 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro383 q ha hb
    | true =>
      simp only [d3359, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51691 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51691, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51692 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54766 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54766, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54766, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54767 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54767, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54767, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5481 (p : Pattern) (ha : d54773 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54768 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54768, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54768, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5480 q ha hb
  have h2 (q : Pattern) (ha : d54769 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54769, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54769, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54770 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54770, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54770, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54771 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54771, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54771, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54772 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54772, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54772, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54773 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54773, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54773, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5482 (p : Pattern) (ha : d54776 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro389 q ha hb
    | true =>
      simp only [d3376, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51717 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51717, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51718 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54775 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54775, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54775, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54776 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54776, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54776, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5483 (p : Pattern) (ha : d54782 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54777 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54777, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54777, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5482 q ha hb
  have h2 (q : Pattern) (ha : d54778 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54778, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54778, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54779 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54779, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54779, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54780 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54780, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54780, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54781 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54781, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54781, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54782 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54782, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54782, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5484 (p : Pattern) (ha : d54786 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro395 q ha hb
    | true =>
      simp only [d3394, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51744 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51744, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51745 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54785 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54785, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54785, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54786 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54786, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54786, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5485 (p : Pattern) (ha : d54792 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54787 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54787, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54787, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5484 q ha hb
  have h2 (q : Pattern) (ha : d54788 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54788, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54788, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54789 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54789, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54789, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54790 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54790, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54790, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54791 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54791, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54791, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54792 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54792, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54792, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5486 (p : Pattern) (ha : d54797 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro401 q ha hb
    | true =>
      simp only [d3413, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51772 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51772, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51773 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54796 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54796, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54796, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54797 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54797, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54797, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5487 (p : Pattern) (ha : d54803 p = 1) (hb : d61744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54798 q = 1) (hb : d61739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54798, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54798, d61739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5486 q ha hb
  have h2 (q : Pattern) (ha : d54799 q = 1) (hb : d61740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54799, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54799, d61740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54800 q = 1) (hb : d61741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54800, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54800, d61741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54801 q = 1) (hb : d61742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54801, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54801, d61742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54802 q = 1) (hb : d61743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54802, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54802, d61743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54803 q = 1) (hb : d61744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54803, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54803, d61744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5488 (p : Pattern) (ha : d54809 p = 1) (hb : d61752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro407 q ha hb
    | true =>
      simp only [d3433, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51801 q = 1) (hb : d61749 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d51801, d61749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51802 q = 1) (hb : d61750 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d61750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54808 q = 1) (hb : d61751 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54808, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54808, d61751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54809 q = 1) (hb : d61752 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54809, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54809, d61752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5489 (p : Pattern) (ha : d54815 p = 1) (hb : d61758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54810 q = 1) (hb : d61753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54810, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54810, d61753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5488 q ha hb
  have h2 (q : Pattern) (ha : d54811 q = 1) (hb : d61754 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54811, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54811, d61754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54812 q = 1) (hb : d61755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54812, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54812, d61755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54813 q = 1) (hb : d61756 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54813, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54813, d61756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54814 q = 1) (hb : d61757 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54814, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54814, d61757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54815 q = 1) (hb : d61758 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54815, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54815, d61758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5490 (p : Pattern) (ha : d54821 p = 1) (hb : d61764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54774 q = 1) (hb : d61709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54774, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5479 q ha hb
    | true =>
      simp only [d54774, d61709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5481 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54783 q = 1) (hb : d61720 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54783, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54783, d61720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5483 q ha hb
  have h3 (q : Pattern) (ha : d54784 q = 1) (hb : d61721 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54784, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54784, d61721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54793 q = 1) (hb : d61732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54793, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54793, d61732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5485 q ha hb
  have h5 (q : Pattern) (ha : d54794 q = 1) (hb : d61733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54794, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54794, d61733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54795 q = 1) (hb : d61734 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54795, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54795, d61734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54804 q = 1) (hb : d61745 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54804, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54804, d61745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5487 q ha hb
  have h8 (q : Pattern) (ha : d54805 q = 1) (hb : d61746 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54805, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54805, d61746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54806 q = 1) (hb : d61747 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54806, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54806, d61747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54807 q = 1) (hb : d61748 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54807, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54807, d61748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54816 q = 1) (hb : d61759 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54816, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54816, d61759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5489 q ha hb
  have h12 (q : Pattern) (ha : d54817 q = 1) (hb : d61760 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54817, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54817, d61760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54818 q = 1) (hb : d61761 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54818, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54818, d61761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54819 q = 1) (hb : d61762 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54819, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54819, d61762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54820 q = 1) (hb : d61763 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54820, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54820, d61763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54821 q = 1) (hb : d61764 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54821, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54821, d61764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5491 (p : Pattern) (ha : d54827 p = 1) (hb : d61770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54822 q = 1) (hb : d61765 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54822, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5490 q ha hb
    | true =>
      simp only [d54822, d61765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54823 q = 1) (hb : d61766 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54823, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54823, d61766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54824 q = 1) (hb : d61767 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54824, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54824, d61767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54825 q = 1) (hb : d61768 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54825, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54825, d61768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54826 q = 1) (hb : d61769 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54826, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54826, d61769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54827 q = 1) (hb : d61770 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54827, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54827, d61770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5492 (p : Pattern) (ha : d54833 p = 1) (hb : d61776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54828 q = 1) (hb : d61771 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54828, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5491 q ha hb
    | true =>
      simp only [d54828, d61771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54829 q = 1) (hb : d61772 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54829, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54829, d61772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54830 q = 1) (hb : d61773 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54830, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54830, d61773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54831 q = 1) (hb : d61774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54831, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54831, d61774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54832 q = 1) (hb : d61775 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54832, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54832, d61775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54833 q = 1) (hb : d61776 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54833, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54833, d61776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5493 (p : Pattern) (ha : d54839 p = 1) (hb : d61782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54834 q = 1) (hb : d61777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54834, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5492 q ha hb
    | true =>
      simp only [d54834, d61777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54835 q = 1) (hb : d61778 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54835, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54835, d61778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54836 q = 1) (hb : d61779 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54836, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54836, d61779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54837 q = 1) (hb : d61780 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54837, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54837, d61780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54838 q = 1) (hb : d61781 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54838, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54838, d61781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54839 q = 1) (hb : d61782 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54839, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54839, d61782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5494 (p : Pattern) (ha : d54845 p = 1) (hb : d61788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54840 q = 1) (hb : d61783 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54840, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5493 q ha hb
    | true =>
      simp only [d54840, d61783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54841 q = 1) (hb : d61784 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54841, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54841, d61784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54842 q = 1) (hb : d61785 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54842, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54842, d61785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54843 q = 1) (hb : d61786 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54843, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54843, d61786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54844 q = 1) (hb : d61787 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54844, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54844, d61787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54845 q = 1) (hb : d61788 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54845, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54845, d61788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5495 (p : Pattern) (ha : d54851 p = 1) (hb : d61794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54846 q = 1) (hb : d61789 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54846, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5494 q ha hb
    | true =>
      simp only [d54846, d61789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54847 q = 1) (hb : d61790 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54847, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54847, d61790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54848 q = 1) (hb : d61791 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54848, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54848, d61791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54849 q = 1) (hb : d61792 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54849, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54849, d61792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54850 q = 1) (hb : d61793 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54850, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54850, d61793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54851 q = 1) (hb : d61794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54851, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54851, d61794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5496 (p : Pattern) (ha : d54857 p = 1) (hb : d61800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54852 q = 1) (hb : d61795 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54852, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5495 q ha hb
    | true =>
      simp only [d54852, d61795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54853 q = 1) (hb : d61796 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54853, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54853, d61796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54854 q = 1) (hb : d61797 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54854, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54854, d61797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54855 q = 1) (hb : d61798 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54855, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54855, d61798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54856 q = 1) (hb : d61799 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54856, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54856, d61799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54857 q = 1) (hb : d61800 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54857, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54857, d61800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5497 (p : Pattern) (ha : d54863 p = 1) (hb : d61806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54858 q = 1) (hb : d61801 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54858, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5496 q ha hb
    | true =>
      simp only [d54858, d61801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54859 q = 1) (hb : d61802 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54859, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54859, d61802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54860 q = 1) (hb : d61803 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54860, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54860, d61803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54861 q = 1) (hb : d61804 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54861, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54861, d61804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54862 q = 1) (hb : d61805 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54862, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54862, d61805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54863 q = 1) (hb : d61806 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54863, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54863, d61806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5498 (p : Pattern) (ha : d61360 p = 1) (hb : d61679 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (ha : d61360 q = 1) (hb : d61679 q = 1) : d61679 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro5499 (p : Pattern) (ha : d52073 p = 1) (hb : d61544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3331 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d52033 q = 1) (hb : d61540 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52034 q = 1) (hb : d61541 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52035 q = 1) (hb : d61542 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52043 q = 1) (hb : d61543 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52043, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52073 q = 1) (hb : d61544 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52073, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
end NetHack.Soko22Hazard87
