import NetHack.Soko22Hazard87.AndIntroBlocks0287
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro72000 (p : Pattern) (ha : d243704 p = 1) (hb : d282251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d282246 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71999 q ha hb
    | true =>
      simp only [d243699, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d282247 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d282248 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d282249 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d282250 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d282251 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72001 (p : Pattern) (ha : d243710 p = 1) (hb : d282257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d282252 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72000 q ha hb
    | true =>
      simp only [d243705, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d282253 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d282254 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d282255 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d282256 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d282257 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72002 (p : Pattern) (ha : d243716 p = 1) (hb : d282263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d282258 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72001 q ha hb
    | true =>
      simp only [d243711, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d282259 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d282260 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d282261 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d282262 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d282263 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72003 (p : Pattern) (ha : d243722 p = 1) (hb : d282269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d282264 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72002 q ha hb
    | true =>
      simp only [d243717, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d282265 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d282266 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d282267 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d282268 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d282269 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72004 (p : Pattern) (ha : d243728 p = 1) (hb : d282275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d282270 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72003 q ha hb
    | true =>
      simp only [d243723, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d282271 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d282272 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d282273 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d282274 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d282275 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72005 (p : Pattern) (ha : d243734 p = 1) (hb : d282281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d282276 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72004 q ha hb
    | true =>
      simp only [d243729, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d282277 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d282278 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d282279 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d282280 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d282281 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro72006 (p : Pattern) (ha : d30721 p = 1) (hb : d245392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30717 q = 1) (hb : d245388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30717, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30718 q = 1) (hb : d245389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30718, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30719 q = 1) (hb : d245390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30719, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30720 q = 1) (hb : d245391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30720, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30721 q = 1) (hb : d245392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30721, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30721, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72007 (p : Pattern) (ha : d30728 p = 1) (hb : d245397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30657 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30717 q = 1) (hb : d245388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30717, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30718 q = 1) (hb : d245389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30718, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30719 q = 1) (hb : d245390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30719, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30720 q = 1) (hb : d245391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d30664 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30724 q = 1) (hb : d245393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30724, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d30725 q = 1) (hb : d245394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30725, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30726 q = 1) (hb : d245395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d245395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30726, d245395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30727 q = 1) (hb : d245396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d245396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30727, d245396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d30728 q = 1) (hb : d245397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30728, d245397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30728, d245397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72008 (p : Pattern) (ha : d245404 p = 1) (hb : d282071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30724 q = 1) (hb : d245393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30724, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30725 q = 1) (hb : d245394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30725, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30726 q = 1) (hb : d245402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d245402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d245402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30727 q = 1) (hb : d245403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d245403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d245403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d282071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d282071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d282071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro72009 (p : Pattern) (ha : d245414 p = 1) (hb : d282081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245410 q = 1) (hb : d282077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d282077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245410, d282077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d282078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d282078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245411, d282078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d282079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d282079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d282079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d282080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d282080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d282080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d282081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d282081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d282081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72010 (p : Pattern) (ha : d245420 p = 1) (hb : d282087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30729 q = 1) (hb : d245398 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d245398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72006 q ha hb
    | true =>
      simp only [d30729, d245398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72007 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30730 q = 1) (hb : d245399 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d245399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30730, d245399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245400 q = 1) (hb : d282069 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d282069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245400, d282069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245401 q = 1) (hb : d282070 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d282070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245401, d282070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245405 q = 1) (hb : d282072 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d282072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245405, d282072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72008 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245406 q = 1) (hb : d282073 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d282073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245406, d282073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245407 q = 1) (hb : d282074 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d282074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245407, d282074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245408 q = 1) (hb : d282075 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d282075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245408, d282075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245409 q = 1) (hb : d282076 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d282076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245409, d282076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245415 q = 1) (hb : d282082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d282082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245415, d282082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72009 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245416 q = 1) (hb : d282083 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d282083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245416, d282083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245417 q = 1) (hb : d282084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d282084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245417, d282084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245418 q = 1) (hb : d282085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d282085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245418, d282085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245419 q = 1) (hb : d282086 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d282086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245419, d282086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245420 q = 1) (hb : d282087 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d282087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245420, d282087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72011 (p : Pattern) (ha : d245426 p = 1) (hb : d282093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d245383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d245383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61343 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d245384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d245384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d245385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d245385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d245386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d245386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d245387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d245387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245421 q = 1) (hb : d282088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d282088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245421, d282088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72010 q ha hb
  have h8 (q : Pattern) (ha : d245422 q = 1) (hb : d282089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d282089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245422, d282089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245423 q = 1) (hb : d282090 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d282090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245423, d282090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245424 q = 1) (hb : d282091 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d282091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245424, d282091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245425 q = 1) (hb : d282092 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d282092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245425, d282092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245426 q = 1) (hb : d282093 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d282093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d245426, d282093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72012 (p : Pattern) (ha : d30935 p = 1) (hb : d245431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30930 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30931 q = 1) (hb : d245427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30931, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30932 q = 1) (hb : d245428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30932, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30933 q = 1) (hb : d245429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30933, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30934 q = 1) (hb : d245430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30934, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30935 q = 1) (hb : d245431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30935, d245431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30935, d245431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72013 (p : Pattern) (ha : d30945 p = 1) (hb : d245436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30930 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30931 q = 1) (hb : d245427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30931, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30932 q = 1) (hb : d245428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30932, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30933 q = 1) (hb : d245429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30933, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30934 q = 1) (hb : d245430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d30940 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30941 q = 1) (hb : d245432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30941, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d30942 q = 1) (hb : d245433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30942, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30943 q = 1) (hb : d245434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d245434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30943, d245434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30944 q = 1) (hb : d245435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d245435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30944, d245435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d30945 q = 1) (hb : d245436 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30945, d245436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30945, d245436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72014 (p : Pattern) (ha : d245443 p = 1) (hb : d282096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30940 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30941 q = 1) (hb : d245432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30941, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30942 q = 1) (hb : d245433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30942, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30943 q = 1) (hb : d245441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d245441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d245441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30944 q = 1) (hb : d245442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d245442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d245442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d282096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d282096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d282096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro72015 (p : Pattern) (ha : d245453 p = 1) (hb : d282107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245449 q = 1) (hb : d282103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d282103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245449, d282103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d282104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d282104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245450, d282104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d282105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d282105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d282105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d282106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d282106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d282106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d282107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d282107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d282107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72016 (p : Pattern) (ha : d245459 p = 1) (hb : d282113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30946 q = 1) (hb : d245437 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d245437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72012 q ha hb
    | true =>
      simp only [d30946, d245437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72013 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30947 q = 1) (hb : d245438 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d245438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30947, d245438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245439 q = 1) (hb : d282094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d282094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245439, d282094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245440 q = 1) (hb : d282095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d282095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245440, d282095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245444 q = 1) (hb : d282097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d282097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245444, d282097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72014 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31113 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245445 q = 1) (hb : d282098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d282098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245445, d282098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245446 q = 1) (hb : d282099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d282099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245446, d282099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245447 q = 1) (hb : d282100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d282100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245447, d282100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245448 q = 1) (hb : d282101 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d282101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245448, d282101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245454 q = 1) (hb : d282108 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d282108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245454, d282108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72015 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245455 q = 1) (hb : d282109 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d282109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245455, d282109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245456 q = 1) (hb : d282110 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d282110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245456, d282110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245457 q = 1) (hb : d282111 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d282111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245457, d282111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245458 q = 1) (hb : d282112 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d282112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245458, d282112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245459 q = 1) (hb : d282113 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d282113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245459, d282113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72017 (p : Pattern) (ha : d245465 p = 1) (hb : d282119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d282114 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d282114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d282114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72016 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d282115 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d282115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d282115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d282116 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d282116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d282116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d282117 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d282117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d282117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d282118 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d282118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d282118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d282119 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d282119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d282119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72018 (p : Pattern) (ha : d31271 p = 1) (hb : d245471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31266 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31267 q = 1) (hb : d245467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31267, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31268 q = 1) (hb : d245468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31268, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31269 q = 1) (hb : d245469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31269, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31270 q = 1) (hb : d245470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31270, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31271 q = 1) (hb : d245471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31271, d245471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31271, d245471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72019 (p : Pattern) (ha : d31281 p = 1) (hb : d245476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31266 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31267 q = 1) (hb : d245467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31267, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31268 q = 1) (hb : d245468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31268, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31269 q = 1) (hb : d245469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31269, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31270 q = 1) (hb : d245470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d31276 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d31277 q = 1) (hb : d245472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31277, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31278 q = 1) (hb : d245473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31278, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31279 q = 1) (hb : d245474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d245474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31279, d245474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31280 q = 1) (hb : d245475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d245475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31280, d245475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d31281 q = 1) (hb : d245476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31281, d245476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31281, d245476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72020 (p : Pattern) (ha : d245483 p = 1) (hb : d282123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31277 q = 1) (hb : d245472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31277, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31278 q = 1) (hb : d245473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31278, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31279 q = 1) (hb : d245481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d245481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d245481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31280 q = 1) (hb : d245482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d245482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d245482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245483 q = 1) (hb : d282123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d282123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245483, d282123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro72021 (p : Pattern) (ha : d245493 p = 1) (hb : d282134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245489 q = 1) (hb : d282130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d282130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245489, d282130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31591 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245490 q = 1) (hb : d282131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d282131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245490, d282131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245491 q = 1) (hb : d282132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d282132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245491, d282132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245492 q = 1) (hb : d282133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d282133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245492, d282133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245493 q = 1) (hb : d282134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d282134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245493, d282134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72022 (p : Pattern) (ha : d245499 p = 1) (hb : d282140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31282 q = 1) (hb : d245477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d245477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72018 q ha hb
    | true =>
      simp only [d31282, d245477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72019 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31283 q = 1) (hb : d245478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d245478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31283, d245478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245479 q = 1) (hb : d282121 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d282121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245479, d282121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245480 q = 1) (hb : d282122 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d282122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245480, d282122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245484 q = 1) (hb : d282124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d282124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245484, d282124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72020 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31470 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245485 q = 1) (hb : d282125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d282125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245485, d282125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245486 q = 1) (hb : d282126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d282126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245486, d282126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245487 q = 1) (hb : d282127 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d282127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245487, d282127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245488 q = 1) (hb : d282128 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d282128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245488, d282128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245494 q = 1) (hb : d282135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d282135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245494, d282135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72021 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31607 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245495 q = 1) (hb : d282136 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d282136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245495, d282136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245496 q = 1) (hb : d282137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d282137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245496, d282137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245497 q = 1) (hb : d282138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d282138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245497, d282138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245498 q = 1) (hb : d282139 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d282139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245498, d282139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245499 q = 1) (hb : d282140 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d282140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245499, d282140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72023 (p : Pattern) (ha : d245505 p = 1) (hb : d282146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245500 q = 1) (hb : d282141 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d282141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245500, d282141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72022 q ha hb
  have h2 (q : Pattern) (ha : d245501 q = 1) (hb : d282142 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d282142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245501, d282142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245502 q = 1) (hb : d282143 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d282143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245502, d282143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245503 q = 1) (hb : d282144 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d282144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245503, d282144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245504 q = 1) (hb : d282145 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d282145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245504, d282145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245505 q = 1) (hb : d282146 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d282146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245505, d282146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72024 (p : Pattern) (ha : d245512 p = 1) (hb : d281154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d281149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245508 q = 1) (hb : d281150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245508, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245509 q = 1) (hb : d281151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245509, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245510 q = 1) (hb : d281152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245510, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245511 q = 1) (hb : d281153 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245511, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245512 q = 1) (hb : d281154 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d281154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d281154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72025 (p : Pattern) (ha : d245517 p = 1) (hb : d281164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d281149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245508 q = 1) (hb : d281150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245508, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245509 q = 1) (hb : d281151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245509, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245510 q = 1) (hb : d281152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245510, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245511 q = 1) (hb : d281153 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245511, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d281159 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245513 q = 1) (hb : d281160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245513, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245514 q = 1) (hb : d281161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245514, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245515 q = 1) (hb : d281162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245515, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245516 q = 1) (hb : d281163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245516, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245517 q = 1) (hb : d281164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d281164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245517, d281164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72026 (p : Pattern) (ha : d245524 p = 1) (hb : d282151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245513 q = 1) (hb : d281160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d281161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245514, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d281162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d281163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d282151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d282151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d282151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72027 (p : Pattern) (ha : d245534 p = 1) (hb : d282162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245530 q = 1) (hb : d282158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d282158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d282158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d282159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d282159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245531, d282159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d282160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d282160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d282160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d282161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d282161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d282161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d282162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d282162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d282162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72028 (p : Pattern) (ha : d245540 p = 1) (hb : d282168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245518 q = 1) (hb : d281165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72024 q ha hb
    | true =>
      simp only [d245518, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72025 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245519 q = 1) (hb : d281166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245519, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245520 q = 1) (hb : d282149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d282149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245520, d282149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245521 q = 1) (hb : d282150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d282150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245521, d282150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245525 q = 1) (hb : d282152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d282152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245525, d282152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72026 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245526 q = 1) (hb : d282153 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d282153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245526, d282153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245527 q = 1) (hb : d282154 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d282154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245527, d282154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245528 q = 1) (hb : d282155 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d282155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245528, d282155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245529 q = 1) (hb : d282156 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d282156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245529, d282156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245535 q = 1) (hb : d282163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d282163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245535, d282163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72027 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245536 q = 1) (hb : d282164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d282164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245536, d282164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245537 q = 1) (hb : d282165 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d282165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245537, d282165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245538 q = 1) (hb : d282166 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d282166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245538, d282166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245539 q = 1) (hb : d282167 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d282167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245539, d282167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245540 q = 1) (hb : d282168 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d282168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245540, d282168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72029 (p : Pattern) (ha : d245546 p = 1) (hb : d282174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d282169 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d282169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d282169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72028 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d282170 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d282170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d282170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d282171 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d282171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d282171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d282172 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d282172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d282172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d282173 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d282173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d282173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d282174 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d282174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d282174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72030 (p : Pattern) (ha : d245554 p = 1) (hb : d281448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d281443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245550 q = 1) (hb : d281444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245550, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245551 q = 1) (hb : d281445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245551, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245552 q = 1) (hb : d281446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245552, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245553 q = 1) (hb : d281447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245553, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245554 q = 1) (hb : d281448 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72031 (p : Pattern) (ha : d245559 p = 1) (hb : d281458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d281443 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245550 q = 1) (hb : d281444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245550, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245551 q = 1) (hb : d281445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245551, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245552 q = 1) (hb : d281446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245552, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245553 q = 1) (hb : d281447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245553, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d281453 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245555 q = 1) (hb : d281454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245555, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245556 q = 1) (hb : d281455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245556, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245557 q = 1) (hb : d281456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245557, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245558 q = 1) (hb : d281457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245558, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245559 q = 1) (hb : d281458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245559, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72032 (p : Pattern) (ha : d245566 p = 1) (hb : d282180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245555 q = 1) (hb : d281454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245555, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d281455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245556, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d281456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d281457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d282180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d282180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d282180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72033 (p : Pattern) (ha : d245576 p = 1) (hb : d282191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245572 q = 1) (hb : d282187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d282187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245572, d282187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d282188 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d282188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245573, d282188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d282189 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d282189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d282189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d282190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d282190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d282190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d282191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d282191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d282191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72034 (p : Pattern) (ha : d245582 p = 1) (hb : d282197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245560 q = 1) (hb : d281459 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d281459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72030 q ha hb
    | true =>
      simp only [d245560, d281459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72031 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245561 q = 1) (hb : d281460 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d281460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245561, d281460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245562 q = 1) (hb : d282178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d282178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245562, d282178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245563 q = 1) (hb : d282179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d282179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245563, d282179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245567 q = 1) (hb : d282181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d282181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245567, d282181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72032 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245568 q = 1) (hb : d282182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d282182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245568, d282182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245569 q = 1) (hb : d282183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d282183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245569, d282183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245570 q = 1) (hb : d282184 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d282184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245570, d282184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245571 q = 1) (hb : d282185 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d282185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245571, d282185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245577 q = 1) (hb : d282192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d282192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245577, d282192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72033 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245578 q = 1) (hb : d282193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d282193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245578, d282193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245579 q = 1) (hb : d282194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d282194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245579, d282194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245580 q = 1) (hb : d282195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d282195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245580, d282195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245581 q = 1) (hb : d282196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d282196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245581, d282196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245582 q = 1) (hb : d282197 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d282197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245582, d282197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72035 (p : Pattern) (ha : d245588 p = 1) (hb : d282203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d282198 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d282198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d282198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72034 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d282199 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d282199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d282199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d282200 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d282200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d282200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d282201 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d282201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d282201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d282202 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d282202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d282202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d282203 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d282203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d282203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72036 (p : Pattern) (ha : d245597 p = 1) (hb : d281770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d281765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245593 q = 1) (hb : d281766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245593, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245594 q = 1) (hb : d281767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245594, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d245595 q = 1) (hb : d281768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245595, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245596 q = 1) (hb : d281769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245596, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245597 q = 1) (hb : d281770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245597, d281770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245597, d281770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro72037 (p : Pattern) (ha : d245602 p = 1) (hb : d281780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d281765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d245593 q = 1) (hb : d281766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245593, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d245594 q = 1) (hb : d281767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245594, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d245595 q = 1) (hb : d281768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245595, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245596 q = 1) (hb : d281769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245596, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d281775 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d245598 q = 1) (hb : d281776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245598, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245599 q = 1) (hb : d281777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245599, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245600 q = 1) (hb : d281778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245600, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245600, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245601 q = 1) (hb : d281779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245601, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245601, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245602 q = 1) (hb : d281780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245602, d281780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245602, d281780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro72038 (p : Pattern) (ha : d245609 p = 1) (hb : d282210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245598 q = 1) (hb : d281776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245598, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245599 q = 1) (hb : d281777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245599, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245607 q = 1) (hb : d281778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245607, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245607, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245608 q = 1) (hb : d281779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245608, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245608, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d282210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d282210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d282210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72039 (p : Pattern) (ha : d245619 p = 1) (hb : d282221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245615 q = 1) (hb : d282217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245615, d282217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245615, d282217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245616 q = 1) (hb : d282218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245616, d282218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245616, d282218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d245617 q = 1) (hb : d282219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245617, d282219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245617, d282219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245618 q = 1) (hb : d282220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245618, d282220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245618, d282220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245619 q = 1) (hb : d282221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245619, d282221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245619, d282221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72040 (p : Pattern) (ha : d245625 p = 1) (hb : d282227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245603 q = 1) (hb : d281781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245603, d281781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72036 q ha hb
    | true =>
      simp only [d245603, d281781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72037 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245604 q = 1) (hb : d281782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245604, d281782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245604, d281782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245605 q = 1) (hb : d282208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245605, d282208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245605, d282208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245606 q = 1) (hb : d282209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245606, d282209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245606, d282209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245610 q = 1) (hb : d282211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245610, d282211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245610, d282211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72038 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245611 q = 1) (hb : d282212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245611, d282212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245611, d282212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d245612 q = 1) (hb : d282213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245612, d282213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245612, d282213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245613 q = 1) (hb : d282214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245613, d282214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245613, d282214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245614 q = 1) (hb : d282215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245614, d282215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245614, d282215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245620 q = 1) (hb : d282222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245620, d282222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245620, d282222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72039 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245621 q = 1) (hb : d282223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245621, d282223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245621, d282223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d245622 q = 1) (hb : d282224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245622, d282224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245622, d282224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245623 q = 1) (hb : d282225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245623, d282225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245623, d282225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245624 q = 1) (hb : d282226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245624, d282226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245624, d282226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245625 q = 1) (hb : d282227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245625, d282227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245625, d282227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72041 (p : Pattern) (ha : d245631 p = 1) (hb : d282233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245626 q = 1) (hb : d282228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245626, d282228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245626, d282228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72040 q ha hb
  have h2 (q : Pattern) (ha : d245627 q = 1) (hb : d282229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245627, d282229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245627, d282229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245628 q = 1) (hb : d282230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245628, d282230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245628, d282230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245629 q = 1) (hb : d282231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245629, d282231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245629, d282231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245630 q = 1) (hb : d282232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245630, d282232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245630, d282232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245631 q = 1) (hb : d282233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245631, d282233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245631, d282233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72042 (p : Pattern) (ha : d245637 p = 1) (hb : d282239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245466 q = 1) (hb : d282120 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245466, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72011 q ha hb
    | true =>
      simp only [d245466, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72017 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245506 q = 1) (hb : d282147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245506, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245506, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72023 q ha hb
  have h3 (q : Pattern) (ha : d245507 q = 1) (hb : d282148 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245507, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245507, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245547 q = 1) (hb : d282175 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245547, d282175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245547, d282175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72029 q ha hb
  have h5 (q : Pattern) (ha : d245548 q = 1) (hb : d282176 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245548, d282176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245548, d282176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245549 q = 1) (hb : d282177 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245549, d282177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245549, d282177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245589 q = 1) (hb : d282204 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245589, d282204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245589, d282204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72035 q ha hb
  have h8 (q : Pattern) (ha : d245590 q = 1) (hb : d282205 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245590, d282205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245590, d282205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245591 q = 1) (hb : d282206 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245591, d282206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245591, d282206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245592 q = 1) (hb : d282207 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245592, d282207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245592, d282207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245632 q = 1) (hb : d282234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245632, d282234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245632, d282234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72041 q ha hb
  have h12 (q : Pattern) (ha : d245633 q = 1) (hb : d282235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245633, d282235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245633, d282235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245634 q = 1) (hb : d282236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245634, d282236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245634, d282236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245635 q = 1) (hb : d282237 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245635, d282237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245635, d282237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245636 q = 1) (hb : d282238 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245636, d282238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245636, d282238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245637 q = 1) (hb : d282239 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245637, d282239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245637, d282239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro72043 (p : Pattern) (ha : d245643 p = 1) (hb : d282245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245638 q = 1) (hb : d282240 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245638, d282240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72042 q ha hb
    | true =>
      simp only [d245638, d282240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245639 q = 1) (hb : d282241 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245639, d282241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245639, d282241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245640 q = 1) (hb : d282242 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245640, d282242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245640, d282242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245641 q = 1) (hb : d282243 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245641, d282243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245641, d282243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245642 q = 1) (hb : d282244 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245642, d282244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245642, d282244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245643 q = 1) (hb : d282245 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245643, d282245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245643, d282245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72044 (p : Pattern) (ha : d245649 p = 1) (hb : d282251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245644 q = 1) (hb : d282246 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245644, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72043 q ha hb
    | true =>
      simp only [d245644, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245645 q = 1) (hb : d282247 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245645, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245645, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245646 q = 1) (hb : d282248 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245646, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245646, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245647 q = 1) (hb : d282249 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245647, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245647, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245648 q = 1) (hb : d282250 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245648, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245648, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245649 q = 1) (hb : d282251 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245649, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245649, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72045 (p : Pattern) (ha : d245655 p = 1) (hb : d282257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245650 q = 1) (hb : d282252 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245650, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72044 q ha hb
    | true =>
      simp only [d245650, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245651 q = 1) (hb : d282253 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245651, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245651, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245652 q = 1) (hb : d282254 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245652, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245652, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245653 q = 1) (hb : d282255 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245653, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245653, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245654 q = 1) (hb : d282256 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245654, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245654, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245655 q = 1) (hb : d282257 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245655, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245655, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72046 (p : Pattern) (ha : d245661 p = 1) (hb : d282263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245656 q = 1) (hb : d282258 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245656, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72045 q ha hb
    | true =>
      simp only [d245656, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245657 q = 1) (hb : d282259 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245657, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245657, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245658 q = 1) (hb : d282260 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245658, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245658, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245659 q = 1) (hb : d282261 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245659, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245659, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245660 q = 1) (hb : d282262 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245660, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245660, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245661 q = 1) (hb : d282263 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245661, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245661, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72047 (p : Pattern) (ha : d245667 p = 1) (hb : d282269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245662 q = 1) (hb : d282264 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245662, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72046 q ha hb
    | true =>
      simp only [d245662, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245663 q = 1) (hb : d282265 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245663, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245663, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245664 q = 1) (hb : d282266 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245664, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245664, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245665 q = 1) (hb : d282267 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245665, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245665, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245666 q = 1) (hb : d282268 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245666, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245666, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245667 q = 1) (hb : d282269 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245667, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245667, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72048 (p : Pattern) (ha : d245673 p = 1) (hb : d282275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245668 q = 1) (hb : d282270 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245668, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72047 q ha hb
    | true =>
      simp only [d245668, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245669 q = 1) (hb : d282271 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245669, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245669, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245670 q = 1) (hb : d282272 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245670, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245670, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245671 q = 1) (hb : d282273 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245671, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245671, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245672 q = 1) (hb : d282274 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245672, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245672, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245673 q = 1) (hb : d282275 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245673, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245673, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72049 (p : Pattern) (ha : d245679 p = 1) (hb : d282281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245674 q = 1) (hb : d282276 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245674, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72048 q ha hb
    | true =>
      simp only [d245674, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245675 q = 1) (hb : d282277 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245675, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245675, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245676 q = 1) (hb : d282278 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245676, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245676, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245677 q = 1) (hb : d282279 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245677, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245677, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245678 q = 1) (hb : d282280 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245678, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245678, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245679 q = 1) (hb : d282281 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245679, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245679, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72050 (p : Pattern) (ha : d18 p = 1) (hb : d282283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261984 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18 q = 1) (hb : d282283 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro72051 (p : Pattern) (ha : d24 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d22 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d23 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d24 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro72052 (p : Pattern) (ha : d30 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72053 (p : Pattern) (ha : d36 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72054 (p : Pattern) (ha : d42 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72055 (p : Pattern) (ha : d48 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72056 (p : Pattern) (ha : d49 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72057 (p : Pattern) (ha : d55 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72058 (p : Pattern) (ha : d60 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72059 (p : Pattern) (ha : d71 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72060 (p : Pattern) (ha : d77 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72061 (p : Pattern) (ha : d83 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72060 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72062 (p : Pattern) (ha : d89 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72063 (p : Pattern) (ha : d95 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72055 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72057 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72058 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72062 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72064 (p : Pattern) (ha : d104 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72065 (p : Pattern) (ha : d111 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72066 (p : Pattern) (ha : d213 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72067 (p : Pattern) (ha : d132 p = 1) (hb : d282283 p = 1) : d38813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17 q = 1) (hb : d261984 q = 1) : d17 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132 q = 1) (hb : d282283 q = 1) : d38813 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d282283, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132, d282283, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro72068 (p : Pattern) (ha : d138 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d136 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d22 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d23 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d138 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72069 (p : Pattern) (ha : d144 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
    | true =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d143 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d144 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d144, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72070 (p : Pattern) (ha : d150 p = 1) (hb : d282284 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
    | true =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d149 q = 1) (hb : d282284 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150 q = 1) (hb : d282284 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72071 (p : Pattern) (ha : d203 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72072 (p : Pattern) (ha : d4349 p = 1) (hb : d282284 p = 1) : d257224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72071 q ha hb
    | true =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d282284 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4341, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d282284 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d282284 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d282284 q = 1) : d257224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d257224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72073 (p : Pattern) (ha : d231 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
    | true =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d230 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72074 (p : Pattern) (ha : d237 p = 1) (hb : d282284 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
    | true =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d282284 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237 q = 1) (hb : d282284 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72075 (p : Pattern) (ha : d243 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72074 q ha hb
    | true =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72060 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72076 (p : Pattern) (ha : d4359 p = 1) (hb : d282284 p = 1) : d257253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72075 q ha hb
    | true =>
      simp only [d244, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d282284 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d282284 q = 1) : d257250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, d257250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d282284 q = 1) : d257251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d257251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d282284 q = 1) : d257252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d257252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d282284 q = 1) : d257253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d257253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72077 (p : Pattern) (ha : d116 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72078 (p : Pattern) (ha : d123 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72079 (p : Pattern) (ha : d156 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72080 (p : Pattern) (ha : d51643 p = 1) (hb : d282284 p = 1) : d257212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
    | true =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d282284 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d282284 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d282284 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d282284 q = 1) : d257212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d257212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72081 (p : Pattern) (ha : d194 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72082 (p : Pattern) (ha : d199 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72083 (p : Pattern) (ha : d51646 p = 1) (hb : d282284 p = 1) : d257219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
    | true =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d282284 q = 1) : d257209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d257209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d282284 q = 1) : d257210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d257210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d282284 q = 1) : d257211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d257211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72081 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72082 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d204 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72071 q ha hb
    | true =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h23 (q : Pattern) (ha : d4340 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4340, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d4341 q = 1) (hb : d282284 q = 1) : d257216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d4341, d257216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51644 q = 1) (hb : d282284 q = 1) : d257217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51644, d257217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d51645 q = 1) (hb : d282284 q = 1) : d257218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51645, d257218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d51646 q = 1) (hb : d282284 q = 1) : d257219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51646, d257219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72084 (p : Pattern) (ha : d51652 p = 1) (hb : d282284 p = 1) : d257259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72064 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72064 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72065 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d282284 q = 1) : d257220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72080 q ha hb
    | true =>
      simp only [d51647, d257220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72083 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72066 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d282284 q = 1) : d257221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d257221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d282284 q = 1) : d257222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d257222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d282284 q = 1) : d257223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d257223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d282284 q = 1) : d257225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d257225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72072 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d282284 q = 1) : d257226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d257226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d282284 q = 1) : d257227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d257227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d282284 q = 1) : d257228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d257228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d282284 q = 1) : d257229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, d257229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d282284 q = 1) : d257254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d257254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72076 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d282284 q = 1) : d257255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d257255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d282284 q = 1) : d257256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d257256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d282284 q = 1) : d257257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d257257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d282284 q = 1) : d257258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d257258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d282284 q = 1) : d257259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, d257259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro72085 (p : Pattern) (ha : d284 p = 1) (hb : d282284 p = 1) : d257269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
    | true =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284 q = 1) (hb : d282284 q = 1) : d257269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d257269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72086 (p : Pattern) (ha : d291 p = 1) (hb : d282284 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
    | true =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72071 q ha hb
    | true =>
      simp only [d204, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h7 (q : Pattern) (ha : d287 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d289 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d291 q = 1) (hb : d282284 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d291, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72087 (p : Pattern) (ha : d397 p = 1) (hb : d282284 p = 1) : d257340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
    | true =>
      simp only [d157, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72054 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d397 q = 1) (hb : d282284 q = 1) : d257340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, d257340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72088 (p : Pattern) (ha : d406 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72089 (p : Pattern) (ha : d462 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72090 (p : Pattern) (ha : d296 p = 1) (hb : d282284 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d296 q = 1) (hb : d282284 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72091 (p : Pattern) (ha : d303 p = 1) (hb : d282284 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d303 q = 1) (hb : d282284 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72092 (p : Pattern) (ha : d4736 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72093 (p : Pattern) (ha : d312 p = 1) (hb : d282283 p = 1) : d285865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d311 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d130 q = 1) : d130 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131 q = 1) (hb : d261984 q = 1) : d33213 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d261984, d33213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131, d261984, d33213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d312 q = 1) (hb : d282283 q = 1) : d285865 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d282283, d285865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312, d282283, d285865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72094 (p : Pattern) (ha : d318 p = 1) (hb : d282284 p = 1) : d285871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d136 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d318 q = 1) (hb : d282284 q = 1) : d285871 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72095 (p : Pattern) (ha : d9381 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d22 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d23 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d9381 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9381, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro72096 (p : Pattern) (ha : d15966 p = 1) (hb : d282284 p = 1) : d285877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
    | true =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
    | true =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d282284 q = 1) : d285876 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12495 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15966 q = 1) (hb : d282284 q = 1) : d285877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72097 (p : Pattern) (ha : d15972 p = 1) (hb : d282284 p = 1) : d285883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72096 q ha hb
    | true =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
    | true =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15971 q = 1) (hb : d282284 q = 1) : d285882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15971, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15972 q = 1) (hb : d282284 q = 1) : d285883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15972, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro72098 (p : Pattern) (ha : d15978 p = 1) (hb : d282284 p = 1) : d285889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72097 q ha hb
    | true =>
      simp only [d15973, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d282284 q = 1) : d285889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72099 (p : Pattern) (ha : d128195 p = 1) (hb : d282284 p = 1) : d285895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d282284 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72090 q ha hb
    | true =>
      simp only [d297, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d282284 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d282284 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d282284 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d282284 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72091 q ha hb
    | true =>
      simp only [d304, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d282284 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d282284 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72098 q ha hb
    | true =>
      simp only [d15979, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d282284 q = 1) : d285891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72092 q ha hb
    | true =>
      simp only [d4737, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d282284 q = 1) : d285892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d282284 q = 1) : d285893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d282284 q = 1) : d285894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128195 q = 1) (hb : d282284 q = 1) : d285895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d285895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d285895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72100 (p : Pattern) (ha : d376 p = 1) (hb : d282284 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d376 q = 1) (hb : d282284 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d376, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72101 (p : Pattern) (ha : d381 p = 1) (hb : d282284 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72053 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d381 q = 1) (hb : d282284 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d381, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72102 (p : Pattern) (ha : d5355 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72103 (p : Pattern) (ha : d15985 p = 1) (hb : d282284 p = 1) : d285896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72097 q ha hb
    | true =>
      simp only [d15973, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72070 q ha hb
    | true =>
      simp only [d151, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d282284 q = 1) : d285896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72104 (p : Pattern) (ha : d128200 p = 1) (hb : d282284 p = 1) : d285902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d282284 q = 1) : d257282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72090 q ha hb
    | true =>
      simp only [d297, d257282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72077 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d282284 q = 1) : d257283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d257283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d282284 q = 1) : d257284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d257284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d282284 q = 1) : d257285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d257285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d282284 q = 1) : d257289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72091 q ha hb
    | true =>
      simp only [d304, d257289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72078 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d282284 q = 1) : d257290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d257290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d282284 q = 1) : d257291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d257291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72098 q ha hb
    | true =>
      simp only [d15979, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72079 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d282284 q = 1) : d285891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, d285891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72092 q ha hb
    | true =>
      simp only [d4737, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d282284 q = 1) : d257208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d257208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d282284 q = 1) : d285892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, d285892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d282284 q = 1) : d285893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, d285893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d282284 q = 1) : d285894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, d285894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d377 q = 1) (hb : d282284 q = 1) : d257324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72100 q ha hb
    | true =>
      simp only [d377, d257324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72081 q ha hb
  have h16 (q : Pattern) (ha : d378 q = 1) (hb : d282284 q = 1) : d257325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d257325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d379 q = 1) (hb : d282284 q = 1) : d257326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d379, d257326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d380 q = 1) (hb : d282284 q = 1) : d257327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d257327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d382 q = 1) (hb : d282284 q = 1) : d257329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72101 q ha hb
    | true =>
      simp only [d382, d257329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72082 q ha hb
  have h20 (q : Pattern) (ha : d383 q = 1) (hb : d282284 q = 1) : d257330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d257330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d384 q = 1) (hb : d282284 q = 1) : d257331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d384, d257331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15986 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72103 q ha hb
    | true =>
      simp only [d15986, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72071 q ha hb
  have h23 (q : Pattern) (ha : d128196 q = 1) (hb : d282284 q = 1) : d285898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128196, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5356 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72102 q ha hb
    | true =>
      simp only [d5356, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5357 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5357, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128197 q = 1) (hb : d282284 q = 1) : d285899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128197, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128198 q = 1) (hb : d282284 q = 1) : d285900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d285900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128198, d285900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128199 q = 1) (hb : d282284 q = 1) : d285901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d285901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128199, d285901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128200 q = 1) (hb : d282284 q = 1) : d285902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d285902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128200, d285902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72105 (p : Pattern) (ha : d128207 p = 1) (hb : d282284 p = 1) : d285909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72103 q ha hb
    | true =>
      simp only [d15986, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72071 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d282284 q = 1) : d285898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d285898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72102 q ha hb
    | true =>
      simp only [d5356, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d282284 q = 1) : d257215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d257215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d282284 q = 1) : d285899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d285899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d282284 q = 1) : d285907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d285907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d285907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d282284 q = 1) : d285908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d285908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d285908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d282284 q = 1) : d285909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d285909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d285909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72106 (p : Pattern) (ha : d5377 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72074 q ha hb
    | true =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72107 (p : Pattern) (ha : d16004 p = 1) (hb : d282284 p = 1) : d285920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
    | true =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72068 q ha hb
    | true =>
      simp only [d139, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d282284 q = 1) : d285919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12603 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16004 q = 1) (hb : d282284 q = 1) : d285920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72108 (p : Pattern) (ha : d16010 p = 1) (hb : d282284 p = 1) : d285926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72107 q ha hb
    | true =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
    | true =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16009 q = 1) (hb : d282284 q = 1) : d285925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16009, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16010 q = 1) (hb : d282284 q = 1) : d285926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16010, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro72109 (p : Pattern) (ha : d16016 p = 1) (hb : d282284 p = 1) : d285932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72108 q ha hb
    | true =>
      simp only [d16011, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72074 q ha hb
    | true =>
      simp only [d238, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d282284 q = 1) : d285929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d282284 q = 1) : d285930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d282284 q = 1) : d285931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d282284 q = 1) : d285932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72110 (p : Pattern) (ha : d128217 p = 1) (hb : d282284 p = 1) : d285938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d282284 q = 1) : d285933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72109 q ha hb
    | true =>
      simp only [d16017, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72075 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d282284 q = 1) : d285934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d285934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d285934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72106 q ha hb
    | true =>
      simp only [d5378, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d282284 q = 1) : d257249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d257249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d282284 q = 1) : d285935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d285935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d285935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d282284 q = 1) : d285936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d285936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d285936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d282284 q = 1) : d285937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d285937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d285937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d282284 q = 1) : d285938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d285938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d285938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72111 (p : Pattern) (ha : d128223 p = 1) (hb : d282284 p = 1) : d285944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d282284 q = 1) : d257270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d257270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72085 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d282284 q = 1) : d257271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d257271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d282284 q = 1) : d257277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72085 q ha hb
    | true =>
      simp only [d292, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72086 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d282284 q = 1) : d257278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d282284 q = 1) : d257279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d257279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d282284 q = 1) : d285903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d285903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72099 q ha hb
    | true =>
      simp only [d128201, d285903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72104 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d282284 q = 1) : d257341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72087 q ha hb
    | true =>
      simp only [d398, d257341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72065 q ha hb
  have h8 (q : Pattern) (ha : d128202 q = 1) (hb : d282284 q = 1) : d285904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d285904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d285904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128203 q = 1) (hb : d282284 q = 1) : d285905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d285905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128203, d285905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128204 q = 1) (hb : d282284 q = 1) : d285906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d285906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d285906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128208 q = 1) (hb : d282284 q = 1) : d285910 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d285910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d285910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72105 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72088 q ha hb
  have h13 (q : Pattern) (ha : d128209 q = 1) (hb : d282284 q = 1) : d285911 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d285911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128209, d285911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128210 q = 1) (hb : d282284 q = 1) : d285912 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d285912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128210, d285912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128211 q = 1) (hb : d282284 q = 1) : d285913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d285913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128211, d285913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128212 q = 1) (hb : d282284 q = 1) : d285914 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d285914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128212, d285914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128218 q = 1) (hb : d282284 q = 1) : d285939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d285939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d285939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72110 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72089 q ha hb
  have h19 (q : Pattern) (ha : d128219 q = 1) (hb : d282284 q = 1) : d285940 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d285940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128219, d285940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128220 q = 1) (hb : d282284 q = 1) : d285941 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d285941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128220, d285941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128221 q = 1) (hb : d282284 q = 1) : d285942 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d285942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128221, d285942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128222 q = 1) (hb : d282284 q = 1) : d285943 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d285943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128222, d285943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128223 q = 1) (hb : d282284 q = 1) : d285944 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d285944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128223, d285944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro72112 (p : Pattern) (ha : d128229 p = 1) (hb : d282284 p = 1) : d285950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72063 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d282284 q = 1) : d257260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d257260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72084 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d282284 q = 1) : d257261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d257261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d282284 q = 1) : d257262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d257262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d282284 q = 1) : d257263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d257263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d282284 q = 1) : d257264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d257264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128224 q = 1) (hb : d282284 q = 1) : d285945 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d285945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128224, d285945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72111 q ha hb
  have h11 (q : Pattern) (ha : d128225 q = 1) (hb : d282284 q = 1) : d285946 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d285946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128225, d285946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128226 q = 1) (hb : d282284 q = 1) : d285947 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d285947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128226, d285947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128227 q = 1) (hb : d282284 q = 1) : d285948 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d285948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128227, d285948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128228 q = 1) (hb : d282284 q = 1) : d285949 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d285949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128228, d285949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128229 q = 1) (hb : d282284 q = 1) : d285950 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d285950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128229, d285950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72113 (p : Pattern) (ha : d481 p = 1) (hb : d282284 p = 1) : d257200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
    | true =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d480 q = 1) (hb : d282284 q = 1) : d257199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, d257199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d481 q = 1) (hb : d282284 q = 1) : d257200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d481, d257200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72114 (p : Pattern) (ha : d491 p = 1) (hb : d282284 p = 1) : d257206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d282284 q = 1) : d257206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d257206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72115 (p : Pattern) (ha : d501 p = 1) (hb : d282284 p = 1) : d257213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d282284 q = 1) : d257205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d257205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d282284 q = 1) : d257213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d257213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72116 (p : Pattern) (ha : d644 p = 1) (hb : d282284 p = 1) : d257276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72114 q ha hb
    | true =>
      simp only [d633, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72115 q ha hb
    | true =>
      simp only [d639, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d282284 q = 1) : d257276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d257276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72117 (p : Pattern) (ha : d653 p = 1) (hb : d282284 p = 1) : d257490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72115 q ha hb
    | true =>
      simp only [d639, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d282284 q = 1) : d257490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72118 (p : Pattern) (ha : d683 p = 1) (hb : d282284 p = 1) : d257241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
    | true =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d282284 q = 1) : d257240 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d257240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d683 q = 1) (hb : d282284 q = 1) : d257241 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d683, d257241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72119 (p : Pattern) (ha : d730 p = 1) (hb : d282284 p = 1) : d257247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72118 q ha hb
    | true =>
      simp only [d684, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d282284 q = 1) : d257244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d257244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d282284 q = 1) : d257245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d257245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d282284 q = 1) : d257246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d257246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d282284 q = 1) : d257247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d257247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72120 (p : Pattern) (ha : d736 p = 1) (hb : d282284 p = 1) : d257536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72119 q ha hb
    | true =>
      simp only [d731, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d282284 q = 1) : d257532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d282284 q = 1) : d257533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d282284 q = 1) : d257534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d282284 q = 1) : d257535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d282284 q = 1) : d257536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72121 (p : Pattern) (ha : d16036 p = 1) (hb : d282284 p = 1) : d285883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72096 q ha hb
    | true =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
    | true =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d475 q = 1) (hb : d282284 q = 1) : d257198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d475, d257198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16035 q = 1) (hb : d282284 q = 1) : d285882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16035, d285882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16036 q = 1) (hb : d282284 q = 1) : d285883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16036, d285883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72122 (p : Pattern) (ha : d16042 p = 1) (hb : d282284 p = 1) : d285889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d282284 q = 1) : d285889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d285889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72123 (p : Pattern) (ha : d16048 p = 1) (hb : d282284 p = 1) : d285955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72122 q ha hb
    | true =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72114 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d282284 q = 1) : d285955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d285955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d285955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72124 (p : Pattern) (ha : d16051 p = 1) (hb : d282284 p = 1) : d285896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d282284 q = 1) : d285888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d285888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d282284 q = 1) : d285896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d285896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72125 (p : Pattern) (ha : d16057 p = 1) (hb : d282284 p = 1) : d285962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72122 q ha hb
    | true =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72114 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72124 q ha hb
    | true =>
      simp only [d16052, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72115 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d282284 q = 1) : d285958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d282284 q = 1) : d285959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d282284 q = 1) : d285960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d282284 q = 1) : d285961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d282284 q = 1) : d285962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d285962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d285962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72126 (p : Pattern) (ha : d16143 p = 1) (hb : d282284 p = 1) : d286044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d282284 q = 1) : d285890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72122 q ha hb
    | true =>
      simp only [d16043, d285890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72114 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d282284 q = 1) : d285951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d285951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d282284 q = 1) : d285952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d285952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d282284 q = 1) : d285953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d285953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d282284 q = 1) : d285954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d285954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d282284 q = 1) : d257207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72114 q ha hb
    | true =>
      simp only [d633, d257207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d282284 q = 1) : d257265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d257265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d282284 q = 1) : d257266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d257266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d282284 q = 1) : d257267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d257267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d282284 q = 1) : d257268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d257268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d282284 q = 1) : d286044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d286044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d286044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72127 (p : Pattern) (ha : d514 p = 1) (hb : d282284 p = 1) : d257281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d282284 q = 1) : d257281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d257281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72128 (p : Pattern) (ha : d524 p = 1) (hb : d282284 p = 1) : d257288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d282284 q = 1) : d257288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d257288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72129 (p : Pattern) (ha : d16062 p = 1) (hb : d282284 p = 1) : d285967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d282284 q = 1) : d285966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d282284 q = 1) : d285967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d285967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d285967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72130 (p : Pattern) (ha : d16069 p = 1) (hb : d282284 p = 1) : d285974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d282284 q = 1) : d285972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d282284 q = 1) : d285973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d282284 q = 1) : d285974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d285974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d285974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72131 (p : Pattern) (ha : d16114 p = 1) (hb : d282284 p = 1) : d286017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d282284 q = 1) : d286014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d282284 q = 1) : d286015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d282284 q = 1) : d286016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d282284 q = 1) : d286017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d286017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d286017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72132 (p : Pattern) (ha : d16081 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12495 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16081 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16081, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72133 (p : Pattern) (ha : d23230 p = 1) (hb : d282284 p = 1) : d285993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23228 q = 1) (hb : d282284 q = 1) : d285991 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23229 q = 1) (hb : d282284 q = 1) : d285992 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5448 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d5449 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d23230 q = 1) (hb : d282284 q = 1) : d285993 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d285993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23230, d285993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro72134 (p : Pattern) (ha : d530 p = 1) (hb : d282283 p = 1) : d285978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d529 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d310 q = 1) : d310 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d311 q = 1) (hb : d261984 q = 1) : d33326 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d311, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d530 q = 1) (hb : d282283 q = 1) : d285978 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d282283, d285978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d530, d282283, d285978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72135 (p : Pattern) (ha : d28739 p = 1) (hb : d282283 p = 1) : d39244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1531 q = 1) : d1531 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9579 q = 1) (hb : d261984 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, d261984, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d9579, d261984, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d28739 q = 1) (hb : d282283 q = 1) : d39244 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28739, d282283, d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28739, d282283, d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72136 (p : Pattern) (ha : d28745 p = 1) (hb : d282284 p = 1) : d285985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28740 q = 1) (hb : d282284 q = 1) : d258107 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72135 q ha hb
    | true =>
      simp only [d28740, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28741 q = 1) (hb : d282284 q = 1) : d258108 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28741, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28742 q = 1) (hb : d282284 q = 1) : d285982 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28742, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28743 q = 1) (hb : d282284 q = 1) : d285983 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28743, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28744 q = 1) (hb : d282284 q = 1) : d285984 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28744, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d317 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d28745 q = 1) (hb : d282284 q = 1) : d285985 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28745, d285985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28745, d285985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro72137 (p : Pattern) (ha : d28750 p = 1) (hb : d282284 p = 1) : d285871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d5448 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5448, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d5449 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5449, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d28750 q = 1) (hb : d282284 q = 1) : d285871 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28750, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28750, d285871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro72138 (p : Pattern) (ha : d28756 p = 1) (hb : d282284 p = 1) : d285999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d282284 q = 1) : d285988 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d282284 q = 1) : d285989 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
    | true =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d282284 q = 1) : d285990 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d285990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d285990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23235 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23235, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28756 q = 1) (hb : d282284 q = 1) : d285999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28756, d285999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28756, d285999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72139 (p : Pattern) (ha : d28762 p = 1) (hb : d282284 p = 1) : d286005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28757 q = 1) (hb : d282284 q = 1) : d286000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28757, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72138 q ha hb
    | true =>
      simp only [d28757, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72096 q ha hb
  have h2 (q : Pattern) (ha : d28758 q = 1) (hb : d282284 q = 1) : d286001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28758, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28758, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28759 q = 1) (hb : d282284 q = 1) : d286002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28759, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28759, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72096 q ha hb
    | true =>
      simp only [d16082, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72132 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28760 q = 1) (hb : d282284 q = 1) : d286003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28760, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28760, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72096 q ha hb
    | true =>
      simp only [d15967, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145 q = 1) (hb : d282284 q = 1) : d257195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72069 q ha hb
    | true =>
      simp only [d145, d257195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72052 q ha hb
  have h12 (q : Pattern) (ha : d146 q = 1) (hb : d282284 q = 1) : d257196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d257196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147 q = 1) (hb : d282284 q = 1) : d257197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d257197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15970 q = 1) (hb : d282284 q = 1) : d285881 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d285881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28761 q = 1) (hb : d282284 q = 1) : d286004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28761, d286004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28761, d286004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28762 q = 1) (hb : d282284 q = 1) : d286005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28762, d286005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28762, d286005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72140 (p : Pattern) (ha : d28768 p = 1) (hb : d282284 p = 1) : d286011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d282284 q = 1) : d286006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d286006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72139 q ha hb
    | true =>
      simp only [d28763, d286006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d282284 q = 1) : d286007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d286007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d286007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d282284 q = 1) : d286008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d286008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d286008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d282284 q = 1) : d286009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d286009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d286009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d282284 q = 1) : d286010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d286010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d286010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28768 q = 1) (hb : d282284 q = 1) : d286011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28768, d286011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28768, d286011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72141 (p : Pattern) (ha : d238875 p = 1) (hb : d282284 p = 1) : d286023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d282284 q = 1) : d285968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72129 q ha hb
    | true =>
      simp only [d16063, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72127 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d282284 q = 1) : d285969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d282284 q = 1) : d285970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d282284 q = 1) : d285971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d282284 q = 1) : d285975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72130 q ha hb
    | true =>
      simp only [d16070, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72128 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d282284 q = 1) : d285976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d282284 q = 1) : d285977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d282284 q = 1) : d286012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d286012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72140 q ha hb
    | true =>
      simp only [d28769, d286012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72122 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d282284 q = 1) : d286013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d286013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d286013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d282284 q = 1) : d286018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72131 q ha hb
    | true =>
      simp only [d16115, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d282284 q = 1) : d286019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d282284 q = 1) : d286020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d286020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d286020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d282284 q = 1) : d286021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d286021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d286021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d282284 q = 1) : d286022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d286022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d286022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238875 q = 1) (hb : d282284 q = 1) : d286023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238875, d286023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238875, d286023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72142 (p : Pattern) (ha : d610 p = 1) (hb : d282284 p = 1) : d257323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d282284 q = 1) : d257204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d257204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d282284 q = 1) : d257280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d257280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d282284 q = 1) : d257323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d257323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72143 (p : Pattern) (ha : d616 p = 1) (hb : d282284 p = 1) : d257328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d282284 q = 1) : d257203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d257203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d282284 q = 1) : d257286 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d257286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d282284 q = 1) : d257287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d257287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d282284 q = 1) : d257328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d257328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72144 (p : Pattern) (ha : d16121 p = 1) (hb : d282284 p = 1) : d286024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d282284 q = 1) : d285887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d285887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d282284 q = 1) : d285966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d285966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d282284 q = 1) : d286024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d286024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d286024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72145 (p : Pattern) (ha : d16126 p = 1) (hb : d282284 p = 1) : d286029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d282284 q = 1) : d257201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72113 q ha hb
    | true =>
      simp only [d482, d257201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d282284 q = 1) : d257202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d257202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d282284 q = 1) : d285886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d285886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d282284 q = 1) : d285972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d285972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d282284 q = 1) : d285973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d285973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d282284 q = 1) : d286029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d286029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d286029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72146 (p : Pattern) (ha : d16135 p = 1) (hb : d282284 p = 1) : d286036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d282284 q = 1) : d286014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d286014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d282284 q = 1) : d286015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d286015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d282284 q = 1) : d286016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d286016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d282284 q = 1) : d286036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d286036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d286036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72147 (p : Pattern) (ha : d28775 p = 1) (hb : d282284 p = 1) : d286033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d282284 q = 1) : d286006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d286006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72139 q ha hb
    | true =>
      simp only [d28763, d286006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d282284 q = 1) : d286007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d286007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d286007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d282284 q = 1) : d285884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72121 q ha hb
    | true =>
      simp only [d16037, d285884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d282284 q = 1) : d285885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d285885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d282284 q = 1) : d286008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d286008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d286008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d282284 q = 1) : d286009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d286009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d286009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d282284 q = 1) : d286010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d286010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d286010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28775 q = 1) (hb : d282284 q = 1) : d286033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28775, d286033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28775, d286033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72148 (p : Pattern) (ha : d238880 p = 1) (hb : d282284 p = 1) : d286042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d282284 q = 1) : d285968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72129 q ha hb
    | true =>
      simp only [d16063, d285968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72127 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d282284 q = 1) : d285969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d285969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d282284 q = 1) : d285970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d285970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d282284 q = 1) : d285971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d285971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d282284 q = 1) : d285975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72130 q ha hb
    | true =>
      simp only [d16070, d285975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72128 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d282284 q = 1) : d285976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d285976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d282284 q = 1) : d285977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d285977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d282284 q = 1) : d286012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d286012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72140 q ha hb
    | true =>
      simp only [d28769, d286012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72122 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d282284 q = 1) : d286013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d286013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d286013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d282284 q = 1) : d286018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72131 q ha hb
    | true =>
      simp only [d16115, d286018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d282284 q = 1) : d286019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d286019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d282284 q = 1) : d286020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d286020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d286020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d282284 q = 1) : d286021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d286021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d286021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d282284 q = 1) : d286022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d286022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d286022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d282284 q = 1) : d286025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d286025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72144 q ha hb
    | true =>
      simp only [d16122, d286025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72142 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d282284 q = 1) : d286026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d286026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d286026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d282284 q = 1) : d286027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d286027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d286027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d282284 q = 1) : d286028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d286028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d286028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d282284 q = 1) : d286030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d286030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72145 q ha hb
    | true =>
      simp only [d16127, d286030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72143 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d282284 q = 1) : d286031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d286031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d286031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d282284 q = 1) : d286032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d286032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d286032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28776 q = 1) (hb : d282284 q = 1) : d286034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d286034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72147 q ha hb
    | true =>
      simp only [d28776, d286034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72124 q ha hb
  have h23 (q : Pattern) (ha : d238876 q = 1) (hb : d282284 q = 1) : d286035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d286035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238876, d286035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d282284 q = 1) : d286037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72146 q ha hb
    | true =>
      simp only [d16136, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d282284 q = 1) : d286038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238877 q = 1) (hb : d282284 q = 1) : d286039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d286039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238877, d286039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238878 q = 1) (hb : d282284 q = 1) : d286040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238878, d286040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238878, d286040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238879 q = 1) (hb : d282284 q = 1) : d286041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238879, d286041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238879, d286041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238880 q = 1) (hb : d282284 q = 1) : d286042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238880, d286042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238880, d286042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72149 (p : Pattern) (ha : d238887 p = 1) (hb : d282284 p = 1) : d286051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28776 q = 1) (hb : d282284 q = 1) : d286034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d286034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72147 q ha hb
    | true =>
      simp only [d28776, d286034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72124 q ha hb
  have h2 (q : Pattern) (ha : d238876 q = 1) (hb : d282284 q = 1) : d286035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d286035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238876, d286035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d282284 q = 1) : d286037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72146 q ha hb
    | true =>
      simp only [d16136, d286037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d282284 q = 1) : d286038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d286038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238877 q = 1) (hb : d282284 q = 1) : d286039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d286039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238877, d286039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238885 q = 1) (hb : d282284 q = 1) : d286049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238885, d286049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238885, d286049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238886 q = 1) (hb : d282284 q = 1) : d286050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238886, d286050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238886, d286050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238887 q = 1) (hb : d282284 q = 1) : d286051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238887, d286051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238887, d286051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72150 (p : Pattern) (ha : d16176 p = 1) (hb : d282284 p = 1) : d285926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72107 q ha hb
    | true =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
    | true =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d282284 q = 1) : d257239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d257239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16175 q = 1) (hb : d282284 q = 1) : d285925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16175, d285925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16176 q = 1) (hb : d282284 q = 1) : d285926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16176, d285926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72151 (p : Pattern) (ha : d16186 p = 1) (hb : d282284 p = 1) : d285932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72150 q ha hb
    | true =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d282284 q = 1) : d257242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72118 q ha hb
    | true =>
      simp only [d684, d257242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d282284 q = 1) : d257243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d257243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d282284 q = 1) : d285929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d285929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d282284 q = 1) : d285930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d285930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d282284 q = 1) : d285931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d285931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d282284 q = 1) : d285932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d285932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72152 (p : Pattern) (ha : d16207 p = 1) (hb : d282284 p = 1) : d286085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72150 q ha hb
    | true =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d282284 q = 1) : d286082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d286082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d286082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d282284 q = 1) : d286083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d286083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d286083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d282284 q = 1) : d286084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d286084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d286084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d282284 q = 1) : d286085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d286085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d286085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72153 (p : Pattern) (ha : d16166 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72051 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12603 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16166 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16166, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72154 (p : Pattern) (ha : d28803 p = 1) (hb : d282284 p = 1) : d286067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d282284 q = 1) : d286057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d282284 q = 1) : d286058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d282284 q = 1) : d286059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d282284 q = 1) : d286060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
    | true =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d282284 q = 1) : d286061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d286061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d286061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72095 q ha hb
    | true =>
      simp only [d9382, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23314 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23314, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d28803 q = 1) (hb : d282284 q = 1) : d286067 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28803, d286067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28803, d286067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72155 (p : Pattern) (ha : d28809 p = 1) (hb : d282284 p = 1) : d286073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28804 q = 1) (hb : d282284 q = 1) : d286068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28804, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72154 q ha hb
    | true =>
      simp only [d28804, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72107 q ha hb
  have h2 (q : Pattern) (ha : d28805 q = 1) (hb : d282284 q = 1) : d286069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28805, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28805, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28806 q = 1) (hb : d282284 q = 1) : d286070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28806, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28806, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72107 q ha hb
    | true =>
      simp only [d16167, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72153 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28807 q = 1) (hb : d282284 q = 1) : d286071 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28807, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28807, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72107 q ha hb
    | true =>
      simp only [d16005, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d232 q = 1) (hb : d282284 q = 1) : d257236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72073 q ha hb
    | true =>
      simp only [d232, d257236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72059 q ha hb
  have h12 (q : Pattern) (ha : d233 q = 1) (hb : d282284 q = 1) : d257237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d257237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234 q = 1) (hb : d282284 q = 1) : d257238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d257238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16008 q = 1) (hb : d282284 q = 1) : d285924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d285924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28808 q = 1) (hb : d282284 q = 1) : d286072 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28808, d286072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28808, d286072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28809 q = 1) (hb : d282284 q = 1) : d286073 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28809, d286073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28809, d286073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72156 (p : Pattern) (ha : d28815 p = 1) (hb : d282284 p = 1) : d286079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28810 q = 1) (hb : d282284 q = 1) : d286074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28810, d286074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72155 q ha hb
    | true =>
      simp only [d28810, d286074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28811 q = 1) (hb : d282284 q = 1) : d286075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28811, d286075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28811, d286075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d282284 q = 1) : d285927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72150 q ha hb
    | true =>
      simp only [d16177, d285927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d282284 q = 1) : d285928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d285928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28812 q = 1) (hb : d282284 q = 1) : d286076 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28812, d286076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28812, d286076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28813 q = 1) (hb : d282284 q = 1) : d286077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28813, d286077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28813, d286077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28814 q = 1) (hb : d282284 q = 1) : d286078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28814, d286078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28814, d286078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28815 q = 1) (hb : d282284 q = 1) : d286079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28815, d286079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28815, d286079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72157 (p : Pattern) (ha : d238897 p = 1) (hb : d282284 p = 1) : d286091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28816 q = 1) (hb : d282284 q = 1) : d286080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28816, d286080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72156 q ha hb
    | true =>
      simp only [d28816, d286080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72151 q ha hb
  have h2 (q : Pattern) (ha : d238893 q = 1) (hb : d282284 q = 1) : d286081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238893, d286081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238893, d286081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d282284 q = 1) : d286086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d286086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72152 q ha hb
    | true =>
      simp only [d16208, d286086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d282284 q = 1) : d286087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d286087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d286087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238894 q = 1) (hb : d282284 q = 1) : d286088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238894, d286088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238894, d286088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238895 q = 1) (hb : d282284 q = 1) : d286089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238895, d286089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238895, d286089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238896 q = 1) (hb : d282284 q = 1) : d286090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238896, d286090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238896, d286090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238897 q = 1) (hb : d282284 q = 1) : d286091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238897, d286091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238897, d286091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72158 (p : Pattern) (ha : d238903 p = 1) (hb : d282284 p = 1) : d286097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d282284 q = 1) : d285956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d285956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d285956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72123 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d282284 q = 1) : d285957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d285957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d285957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d282284 q = 1) : d285963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72123 q ha hb
    | true =>
      simp only [d16058, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72125 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d282284 q = 1) : d285964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d282284 q = 1) : d285965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d285965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d285965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238881 q = 1) (hb : d282284 q = 1) : d286043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238881, d286043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72141 q ha hb
    | true =>
      simp only [d238881, d286043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72148 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d282284 q = 1) : d286045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d286045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72126 q ha hb
    | true =>
      simp only [d16144, d286045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72116 q ha hb
  have h8 (q : Pattern) (ha : d238882 q = 1) (hb : d282284 q = 1) : d286046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238882, d286046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238882, d286046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238883 q = 1) (hb : d282284 q = 1) : d286047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238883, d286047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238883, d286047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238884 q = 1) (hb : d282284 q = 1) : d286048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238884, d286048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238884, d286048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238888 q = 1) (hb : d282284 q = 1) : d286052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238888, d286052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238888, d286052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72149 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d282284 q = 1) : d257491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72117 q ha hb
  have h13 (q : Pattern) (ha : d238889 q = 1) (hb : d282284 q = 1) : d286053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238889, d286053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238889, d286053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238890 q = 1) (hb : d282284 q = 1) : d286054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238890, d286054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238890, d286054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238891 q = 1) (hb : d282284 q = 1) : d286055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238891, d286055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238891, d286055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238892 q = 1) (hb : d282284 q = 1) : d286056 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238892, d286056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238892, d286056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238898 q = 1) (hb : d282284 q = 1) : d286092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238898, d286092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238898, d286092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72157 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d282284 q = 1) : d257537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72120 q ha hb
  have h19 (q : Pattern) (ha : d238899 q = 1) (hb : d282284 q = 1) : d286093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238899, d286093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238899, d286093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238900 q = 1) (hb : d282284 q = 1) : d286094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238900, d286094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238900, d286094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238901 q = 1) (hb : d282284 q = 1) : d286095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238901, d286095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238901, d286095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238902 q = 1) (hb : d282284 q = 1) : d286096 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238902, d286096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238902, d286096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238903 q = 1) (hb : d282284 q = 1) : d286097 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238903, d286097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238903, d286097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro72159 (p : Pattern) (ha : d238909 p = 1) (hb : d282284 p = 1) : d286103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238904 q = 1) (hb : d282284 q = 1) : d286098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238904, d286098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238904, d286098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72158 q ha hb
  have h2 (q : Pattern) (ha : d238905 q = 1) (hb : d282284 q = 1) : d286099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238905, d286099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238905, d286099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238906 q = 1) (hb : d282284 q = 1) : d286100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238906, d286100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238906, d286100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238907 q = 1) (hb : d282284 q = 1) : d286101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238907, d286101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238907, d286101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238908 q = 1) (hb : d282284 q = 1) : d286102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238908, d286102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238908, d286102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238909 q = 1) (hb : d282284 q = 1) : d286103 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238909, d286103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238909, d286103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72160 (p : Pattern) (ha : d750 p = 1) (hb : d282284 p = 1) : d257188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d136 q = 1) (hb : d282284 q = 1) : d257186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136, d257186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d282284 q = 1) : d257187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137, d257187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d750 q = 1) (hb : d282284 q = 1) : d257188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d750, d257188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h10 p ha hb
theorem andIntro72161 (p : Pattern) (ha : d758 p = 1) (hb : d282284 p = 1) : d285877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
    | true =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d282284 q = 1) : d285876 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d285876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d282284 q = 1) : d285877 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d285877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72162 (p : Pattern) (ha : d762 p = 1) (hb : d282284 p = 1) : d257194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d282284 q = 1) : d257194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d257194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72163 (p : Pattern) (ha : d773 p = 1) (hb : d282284 p = 1) : d286111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72161 q ha hb
    | true =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72162 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d282284 q = 1) : d286105 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d282284 q = 1) : d286110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d286110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d286110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d282284 q = 1) : d286111 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d286111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d286111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72164 (p : Pattern) (ha : d783 p = 1) (hb : d282284 p = 1) : d286121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d282284 q = 1) : d286120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d282284 q = 1) : d286121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d286121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d286121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72165 (p : Pattern) (ha : d793 p = 1) (hb : d282284 p = 1) : d286131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d282284 q = 1) : d286120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d286120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d282284 q = 1) : d286131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d286131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d286131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72166 (p : Pattern) (ha : d950 p = 1) (hb : d282284 p = 1) : d286246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d282284 q = 1) : d286235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72164 q ha hb
    | true =>
      simp only [d939, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d282284 q = 1) : d286236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d282284 q = 1) : d286237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d282284 q = 1) : d286238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d282284 q = 1) : d286239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d282284 q = 1) : d286241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72165 q ha hb
    | true =>
      simp only [d945, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d282284 q = 1) : d286242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d282284 q = 1) : d286243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d282284 q = 1) : d286244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d282284 q = 1) : d286245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d282284 q = 1) : d286246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d286246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d286246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72167 (p : Pattern) (ha : d959 p = 1) (hb : d282284 p = 1) : d286255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d282284 q = 1) : d286241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72165 q ha hb
    | true =>
      simp only [d945, d286241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d282284 q = 1) : d286242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d286242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d282284 q = 1) : d286243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d286243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d282284 q = 1) : d286244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d286244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d282284 q = 1) : d286245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d286245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d282284 q = 1) : d286255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d286255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d286255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72168 (p : Pattern) (ha : d981 p = 1) (hb : d282284 p = 1) : d285920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72094 q ha hb
    | true =>
      simp only [d319, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d282284 q = 1) : d285919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d285919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d282284 q = 1) : d285920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d285920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72169 (p : Pattern) (ha : d986 p = 1) (hb : d282284 p = 1) : d257235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d282284 q = 1) : d257235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d257235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72170 (p : Pattern) (ha : d1005 p = 1) (hb : d282284 p = 1) : d286298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72168 q ha hb
    | true =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72169 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d282284 q = 1) : d286288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d282284 q = 1) : d286297 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d286297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d286297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d282284 q = 1) : d286298 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d286298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d286298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72171 (p : Pattern) (ha : d1063 p = 1) (hb : d282284 p = 1) : d286321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d282284 q = 1) : d286299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72170 q ha hb
    | true =>
      simp only [d1006, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d282284 q = 1) : d286300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d282284 q = 1) : d286318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d286318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d286318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d282284 q = 1) : d286319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d286319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d286319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d282284 q = 1) : d286320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d286320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d286320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d282284 q = 1) : d286321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d286321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d286321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72172 (p : Pattern) (ha : d1069 p = 1) (hb : d282284 p = 1) : d286327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d282284 q = 1) : d286322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d286322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72171 q ha hb
    | true =>
      simp only [d1064, d286322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d282284 q = 1) : d286323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d286323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d286323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d282284 q = 1) : d286324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d286324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d286324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d282284 q = 1) : d286325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d286325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d286325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d282284 q = 1) : d286326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d286326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d286326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d282284 q = 1) : d286327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d286327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d286327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72173 (p : Pattern) (ha : d28836 p = 1) (hb : d282284 p = 1) : d285999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d282284 q = 1) : d285988 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d282284 q = 1) : d285989 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
    | true =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d282284 q = 1) : d285874 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d285874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d282284 q = 1) : d285875 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d285875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d282284 q = 1) : d285990 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d285990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d285990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28835 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28835, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28836 q = 1) (hb : d282284 q = 1) : d285999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28836, d285999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28836, d285999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72174 (p : Pattern) (ha : d28842 p = 1) (hb : d282284 p = 1) : d286107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28837 q = 1) (hb : d282284 q = 1) : d286000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72173 q ha hb
    | true =>
      simp only [d28837, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72161 q ha hb
  have h2 (q : Pattern) (ha : d28838 q = 1) (hb : d282284 q = 1) : d286001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28839 q = 1) (hb : d282284 q = 1) : d286002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72161 q ha hb
    | true =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72162 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28840 q = 1) (hb : d282284 q = 1) : d286003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28840, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d282284 q = 1) : d286105 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d286105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28841 q = 1) (hb : d282284 q = 1) : d286106 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28841, d286106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28841, d286106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28842 q = 1) (hb : d282284 q = 1) : d286107 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28842, d286107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28842, d286107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72175 (p : Pattern) (ha : d28848 p = 1) (hb : d282284 p = 1) : d286117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d282284 q = 1) : d286115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d282284 q = 1) : d286116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d286116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d286116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28848 q = 1) (hb : d282284 q = 1) : d286117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28848, d286117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28848, d286117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72176 (p : Pattern) (ha : d28854 p = 1) (hb : d282284 p = 1) : d286127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d282284 q = 1) : d286122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72175 q ha hb
    | true =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72164 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d282284 q = 1) : d286123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d282284 q = 1) : d286124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d282284 q = 1) : d286125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d282284 q = 1) : d286126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28854 q = 1) (hb : d282284 q = 1) : d286127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28854, d286127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28854, d286127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72177 (p : Pattern) (ha : d28857 p = 1) (hb : d282284 p = 1) : d286130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d282284 q = 1) : d286115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d282284 q = 1) : d286116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d286116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d286116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28857 q = 1) (hb : d282284 q = 1) : d286130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28857, d286130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28857, d286130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72178 (p : Pattern) (ha : d28863 p = 1) (hb : d282284 p = 1) : d286137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d282284 q = 1) : d286122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72175 q ha hb
    | true =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72164 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d282284 q = 1) : d286123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d282284 q = 1) : d286124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d282284 q = 1) : d286125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d282284 q = 1) : d286126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28858 q = 1) (hb : d282284 q = 1) : d286132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72177 q ha hb
    | true =>
      simp only [d28858, d286132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72165 q ha hb
  have h7 (q : Pattern) (ha : d28859 q = 1) (hb : d282284 q = 1) : d286133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d286133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28860 q = 1) (hb : d282284 q = 1) : d286134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28860, d286134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28861 q = 1) (hb : d282284 q = 1) : d286135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d286135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28862 q = 1) (hb : d282284 q = 1) : d286136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d286136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28863 q = 1) (hb : d282284 q = 1) : d286137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28863, d286137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28863, d286137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72179 (p : Pattern) (ha : d28985 p = 1) (hb : d282284 p = 1) : d286240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d282284 q = 1) : d286122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72175 q ha hb
    | true =>
      simp only [d28849, d286122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72164 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d282284 q = 1) : d286123 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d286123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d282284 q = 1) : d286124 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d286124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d282284 q = 1) : d286125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d286125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d282284 q = 1) : d286126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d286126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d282284 q = 1) : d286235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72164 q ha hb
    | true =>
      simp only [d939, d286235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d282284 q = 1) : d286236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d286236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d282284 q = 1) : d286237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d286237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d282284 q = 1) : d286238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d286238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d282284 q = 1) : d286239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d286239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28985 q = 1) (hb : d282284 q = 1) : d286240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28985, d286240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28985, d286240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72180 (p : Pattern) (ha : d806 p = 1) (hb : d282284 p = 1) : d286144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d282284 q = 1) : d286143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d282284 q = 1) : d286144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d286144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d286144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72181 (p : Pattern) (ha : d816 p = 1) (hb : d282284 p = 1) : d286154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d282284 q = 1) : d286152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d282284 q = 1) : d286153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d282284 q = 1) : d286154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d286154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d286154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72182 (p : Pattern) (ha : d28868 p = 1) (hb : d282284 p = 1) : d286142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d282284 q = 1) : d286115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d282284 q = 1) : d286141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d286141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d286141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28868 q = 1) (hb : d282284 q = 1) : d286142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28868, d286142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28868, d286142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72183 (p : Pattern) (ha : d28875 p = 1) (hb : d282284 p = 1) : d286151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d282284 q = 1) : d286149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d286149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d286149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d282284 q = 1) : d286150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d286150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d286150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28875 q = 1) (hb : d282284 q = 1) : d286151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28875, d286151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28875, d286151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72184 (p : Pattern) (ha : d23421 p = 1) (hb : d282284 p = 1) : d286178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23419 q = 1) (hb : d282284 q = 1) : d286176 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23420 q = 1) (hb : d282284 q = 1) : d286177 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23228 q = 1) (hb : d282284 q = 1) : d285991 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d23229 q = 1) (hb : d282284 q = 1) : d285992 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d23421 q = 1) (hb : d282284 q = 1) : d286178 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d286178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23421, d286178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro72185 (p : Pattern) (ha : d821 p = 1) (hb : d282283 p = 1) : d286158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d820 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d528 q = 1) : d528 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d529 q = 1) (hb : d261984 q = 1) : d33553 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d529, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d821 q = 1) (hb : d282283 q = 1) : d286158 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d821, d282283, d286158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d821, d282283, d286158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72186 (p : Pattern) (ha : d28879 p = 1) (hb : d282283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d826 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261984 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28879 q = 1) (hb : d282283 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28879, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28879, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro72187 (p : Pattern) (ha : d28882 p = 1) (hb : d282283 p = 1) : d39244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1532 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1531 q = 1) : d1531 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9579 q = 1) (hb : d261984 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, d261984, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d9579, d261984, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d28882 q = 1) (hb : d282283 q = 1) : d39244 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28882, d282283, d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28882, d282283, d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72188 (p : Pattern) (ha : d28891 p = 1) (hb : d282284 p = 1) : d286165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d282284 q = 1) : d286159 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72185 q ha hb
    | true =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d282284 q = 1) : d286160 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d282284 q = 1) : d286161 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28880 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72186 q ha hb
    | true =>
      simp only [d28880, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28881 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d28883 q = 1) (hb : d282284 q = 1) : d258107 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72187 q ha hb
    | true =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28884 q = 1) (hb : d282284 q = 1) : d258108 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28885 q = 1) (hb : d282284 q = 1) : d286162 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28885, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28886 q = 1) (hb : d282284 q = 1) : d286163 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28886, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28887 q = 1) (hb : d282284 q = 1) : d286164 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28887, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d28888 q = 1) (hb : d282284 q = 1) : d285982 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28888, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28888, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d28889 q = 1) (hb : d282284 q = 1) : d285983 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28889, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28889, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28890 q = 1) (hb : d282284 q = 1) : d285984 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28890, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28890, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h22 (q : Pattern) (ha : d28891 q = 1) (hb : d282284 q = 1) : d286165 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28891, d286165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28891, d286165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro72189 (p : Pattern) (ha : d28896 p = 1) (hb : d282284 p = 1) : d286170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28740 q = 1) (hb : d282284 q = 1) : d258107 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72135 q ha hb
    | true =>
      simp only [d28740, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28741 q = 1) (hb : d282284 q = 1) : d258108 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28741, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28742 q = 1) (hb : d282284 q = 1) : d285982 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28742, d285982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28743 q = 1) (hb : d282284 q = 1) : d285983 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28743, d285983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28744 q = 1) (hb : d282284 q = 1) : d285984 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28744, d285984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d23228 q = 1) (hb : d282284 q = 1) : d285991 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23228, d285991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d23229 q = 1) (hb : d282284 q = 1) : d285992 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23229, d285992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d28896 q = 1) (hb : d282284 q = 1) : d286170 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28896, d286170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28896, d286170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72190 (p : Pattern) (ha : d28902 p = 1) (hb : d282284 p = 1) : d286184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d282284 q = 1) : d286166 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72188 q ha hb
    | true =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d282284 q = 1) : d286167 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d282284 q = 1) : d286168 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d286168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d286168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d282284 q = 1) : d286169 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d286169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d286169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d282284 q = 1) : d286171 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72189 q ha hb
    | true =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d282284 q = 1) : d286172 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d282284 q = 1) : d286173 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d286173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d286173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d282284 q = 1) : d286174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d286174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d286174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d282284 q = 1) : d286175 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d286175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d286175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d282284 q = 1) : d286179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
    | true =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d282284 q = 1) : d286180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d282284 q = 1) : d286181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d282284 q = 1) : d286182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23233 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23234 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23426 q = 1) (hb : d282284 q = 1) : d286183 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d286183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23426, d286183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28902 q = 1) (hb : d282284 q = 1) : d286184 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28902, d286184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28902, d286184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72191 (p : Pattern) (ha : d28906 p = 1) (hb : d282284 p = 1) : d286188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d282284 q = 1) : d285996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d285996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d282284 q = 1) : d285997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d285997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d282284 q = 1) : d257191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d257191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d282284 q = 1) : d257192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d257192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28835 q = 1) (hb : d282284 q = 1) : d285998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28835, d285998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d282284 q = 1) : d257193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d257193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28906 q = 1) (hb : d282284 q = 1) : d286188 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28906, d286188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28906, d286188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72192 (p : Pattern) (ha : d28912 p = 1) (hb : d282284 p = 1) : d286194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28903 q = 1) (hb : d282284 q = 1) : d286185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28903, d286185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72190 q ha hb
    | true =>
      simp only [d28903, d286185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72173 q ha hb
  have h2 (q : Pattern) (ha : d28904 q = 1) (hb : d282284 q = 1) : d286186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28904, d286186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28904, d286186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28905 q = 1) (hb : d282284 q = 1) : d286187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28905, d286187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28905, d286187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28907 q = 1) (hb : d282284 q = 1) : d286189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28907, d286189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72173 q ha hb
    | true =>
      simp only [d28907, d286189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72191 q ha hb
  have h5 (q : Pattern) (ha : d28908 q = 1) (hb : d282284 q = 1) : d286190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28908, d286190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28908, d286190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28909 q = 1) (hb : d282284 q = 1) : d286191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28909, d286191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28909, d286191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28910 q = 1) (hb : d282284 q = 1) : d286192 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28910, d286192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28910, d286192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28837 q = 1) (hb : d282284 q = 1) : d286000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72173 q ha hb
    | true =>
      simp only [d28837, d286000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72161 q ha hb
  have h9 (q : Pattern) (ha : d28838 q = 1) (hb : d282284 q = 1) : d286001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d286001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28839 q = 1) (hb : d282284 q = 1) : d286002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d286002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d282284 q = 1) : d285878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72161 q ha hb
    | true =>
      simp only [d763, d285878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72162 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d282284 q = 1) : d285879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d285879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d282284 q = 1) : d285880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d285880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28840 q = 1) (hb : d282284 q = 1) : d286003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28840, d286003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28911 q = 1) (hb : d282284 q = 1) : d286193 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28911, d286193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28911, d286193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28912 q = 1) (hb : d282284 q = 1) : d286194 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28912, d286194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28912, d286194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72193 (p : Pattern) (ha : d28918 p = 1) (hb : d282284 p = 1) : d286200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d282284 q = 1) : d286195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d286195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72192 q ha hb
    | true =>
      simp only [d28913, d286195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d282284 q = 1) : d286196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d286196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d286196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d282284 q = 1) : d286197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d286197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d286197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d282284 q = 1) : d286198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d286198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d286198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d282284 q = 1) : d286199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d286199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d286199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28918 q = 1) (hb : d282284 q = 1) : d286200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28918, d286200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28918, d286200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72194 (p : Pattern) (ha : d28956 p = 1) (hb : d282284 p = 1) : d286206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d282284 q = 1) : d286203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d286203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d286203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d282284 q = 1) : d286204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d286204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d286204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d282284 q = 1) : d286205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d286205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d286205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28956 q = 1) (hb : d282284 q = 1) : d286206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28956, d286206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28956, d286206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72195 (p : Pattern) (ha : d238915 p = 1) (hb : d282284 p = 1) : d286212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d282284 q = 1) : d286145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d286145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72182 q ha hb
    | true =>
      simp only [d28869, d286145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72180 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d282284 q = 1) : d286146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d286146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d286146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d282284 q = 1) : d286147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d286147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d286147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d282284 q = 1) : d286148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d286148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d286148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d282284 q = 1) : d286155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d286155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72183 q ha hb
    | true =>
      simp only [d28876, d286155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72181 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d282284 q = 1) : d286156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d286156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d286156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d282284 q = 1) : d286157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d286157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d286157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d282284 q = 1) : d286201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d286201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72193 q ha hb
    | true =>
      simp only [d28919, d286201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72175 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d282284 q = 1) : d286202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d286202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d286202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d282284 q = 1) : d286207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d286207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72194 q ha hb
    | true =>
      simp only [d28957, d286207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d282284 q = 1) : d286208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d286208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d286208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d282284 q = 1) : d286209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d286209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d286209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d282284 q = 1) : d286210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d286210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d286210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d282284 q = 1) : d286211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d286211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d286211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238915 q = 1) (hb : d282284 q = 1) : d286212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238915, d286212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238915, d286212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72196 (p : Pattern) (ha : d916 p = 1) (hb : d282284 p = 1) : d286214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d282284 q = 1) : d286119 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d286119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d282284 q = 1) : d286143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d286143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d282284 q = 1) : d286214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d286214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d286214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72197 (p : Pattern) (ha : d922 p = 1) (hb : d282284 p = 1) : d286220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d282284 q = 1) : d286118 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d286118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d282284 q = 1) : d286152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d286152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d282284 q = 1) : d286153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d286153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d282284 q = 1) : d286220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d286220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d286220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72198 (p : Pattern) (ha : d28963 p = 1) (hb : d282284 p = 1) : d286213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d282284 q = 1) : d286115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d286115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d282284 q = 1) : d286141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d286141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d286141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28963 q = 1) (hb : d282284 q = 1) : d286213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28963, d286213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28963, d286213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72199 (p : Pattern) (ha : d28968 p = 1) (hb : d282284 p = 1) : d286219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d282284 q = 1) : d286112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72163 q ha hb
    | true =>
      simp only [d774, d286112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d282284 q = 1) : d286113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d286113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d282284 q = 1) : d286114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d286114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d282284 q = 1) : d286149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d286149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d286149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d282284 q = 1) : d286150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d286150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d286150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28968 q = 1) (hb : d282284 q = 1) : d286219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28968, d286219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28968, d286219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72200 (p : Pattern) (ha : d28972 p = 1) (hb : d282284 p = 1) : d286224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d282284 q = 1) : d286195 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d286195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72192 q ha hb
    | true =>
      simp only [d28913, d286195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d282284 q = 1) : d286196 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d286196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d286196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d282284 q = 1) : d286197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d286197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d286197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d282284 q = 1) : d286198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d286198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d286198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d282284 q = 1) : d286199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d286199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d286199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28972 q = 1) (hb : d282284 q = 1) : d286224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28972, d286224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28972, d286224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72201 (p : Pattern) (ha : d28977 p = 1) (hb : d282284 p = 1) : d286227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d282284 q = 1) : d286108 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72174 q ha hb
    | true =>
      simp only [d28843, d286108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d282284 q = 1) : d286109 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d286109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d282284 q = 1) : d286203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d286203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d286203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d282284 q = 1) : d286204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d286204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d286204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d282284 q = 1) : d286205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d286205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d286205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28977 q = 1) (hb : d282284 q = 1) : d286227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28977, d286227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28977, d286227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72202 (p : Pattern) (ha : d238920 p = 1) (hb : d282284 p = 1) : d286233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d282284 q = 1) : d286145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d286145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72182 q ha hb
    | true =>
      simp only [d28869, d286145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72180 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d282284 q = 1) : d286146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d286146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d286146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d282284 q = 1) : d286147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d286147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d286147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d282284 q = 1) : d286148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d286148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d286148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d282284 q = 1) : d286155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d286155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72183 q ha hb
    | true =>
      simp only [d28876, d286155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72181 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d282284 q = 1) : d286156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d286156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d286156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d282284 q = 1) : d286157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d286157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d286157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d282284 q = 1) : d286201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d286201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72193 q ha hb
    | true =>
      simp only [d28919, d286201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72175 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d282284 q = 1) : d286202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d286202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d286202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d282284 q = 1) : d286207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d286207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72194 q ha hb
    | true =>
      simp only [d28957, d286207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d282284 q = 1) : d286208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d286208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d286208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d282284 q = 1) : d286209 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d286209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d286209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d282284 q = 1) : d286210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d286210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d286210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d282284 q = 1) : d286211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d286211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d286211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28964 q = 1) (hb : d282284 q = 1) : d286215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28964, d286215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72198 q ha hb
    | true =>
      simp only [d28964, d286215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72196 q ha hb
  have h16 (q : Pattern) (ha : d28965 q = 1) (hb : d282284 q = 1) : d286216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28965, d286216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28965, d286216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28966 q = 1) (hb : d282284 q = 1) : d286217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28966, d286217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28966, d286217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28967 q = 1) (hb : d282284 q = 1) : d286218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28967, d286218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28967, d286218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28969 q = 1) (hb : d282284 q = 1) : d286221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28969, d286221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72199 q ha hb
    | true =>
      simp only [d28969, d286221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72197 q ha hb
  have h20 (q : Pattern) (ha : d28970 q = 1) (hb : d282284 q = 1) : d286222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28970, d286222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28970, d286222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28971 q = 1) (hb : d282284 q = 1) : d286223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28971, d286223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28971, d286223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28973 q = 1) (hb : d282284 q = 1) : d286225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d286225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72200 q ha hb
    | true =>
      simp only [d28973, d286225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72177 q ha hb
  have h23 (q : Pattern) (ha : d238916 q = 1) (hb : d282284 q = 1) : d286226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d286226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238916, d286226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d28978 q = 1) (hb : d282284 q = 1) : d286228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d286228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72201 q ha hb
    | true =>
      simp only [d28978, d286228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d28979 q = 1) (hb : d282284 q = 1) : d286229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d286229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d28979, d286229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238917 q = 1) (hb : d282284 q = 1) : d286230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d286230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238917, d286230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238918 q = 1) (hb : d282284 q = 1) : d286231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238918, d286231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238918, d286231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238919 q = 1) (hb : d282284 q = 1) : d286232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238919, d286232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238919, d286232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238920 q = 1) (hb : d282284 q = 1) : d286233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238920, d286233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238920, d286233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro72203 (p : Pattern) (ha : d238927 p = 1) (hb : d282284 p = 1) : d286253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28973 q = 1) (hb : d282284 q = 1) : d286225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d286225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72200 q ha hb
    | true =>
      simp only [d28973, d286225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72177 q ha hb
  have h2 (q : Pattern) (ha : d238916 q = 1) (hb : d282284 q = 1) : d286226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d286226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238916, d286226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28978 q = 1) (hb : d282284 q = 1) : d286228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d286228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72201 q ha hb
    | true =>
      simp only [d28978, d286228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28979 q = 1) (hb : d282284 q = 1) : d286229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d286229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28979, d286229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238917 q = 1) (hb : d282284 q = 1) : d286230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d286230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238917, d286230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238925 q = 1) (hb : d282284 q = 1) : d286251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238925, d286251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238925, d286251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238926 q = 1) (hb : d282284 q = 1) : d286252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238926, d286252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238926, d286252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238927 q = 1) (hb : d282284 q = 1) : d286253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238927, d286253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238927, d286253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72204 (p : Pattern) (ha : d29007 p = 1) (hb : d282284 p = 1) : d286275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28998 q = 1) (hb : d282284 q = 1) : d286261 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28998, d286261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28998, d286261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72188 q ha hb
  have h2 (q : Pattern) (ha : d28892 q = 1) (hb : d282284 q = 1) : d286166 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72188 q ha hb
    | true =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28999 q = 1) (hb : d282284 q = 1) : d286262 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28999, d286262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28999, d286262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28893 q = 1) (hb : d282284 q = 1) : d286167 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29000 q = 1) (hb : d282284 q = 1) : d286263 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29000, d286263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29000, d286263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29001 q = 1) (hb : d282284 q = 1) : d286264 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29001, d286264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29001, d286264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29002 q = 1) (hb : d282284 q = 1) : d286265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29002, d286265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29002, d286265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72189 q ha hb
  have h8 (q : Pattern) (ha : d28897 q = 1) (hb : d282284 q = 1) : d286171 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72189 q ha hb
    | true =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29003 q = 1) (hb : d282284 q = 1) : d286266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29003, d286266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29003, d286266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28898 q = 1) (hb : d282284 q = 1) : d286172 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29004 q = 1) (hb : d282284 q = 1) : d286267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29004, d286267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29004, d286267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29005 q = 1) (hb : d282284 q = 1) : d286268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29005, d286268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29005, d286268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29006 q = 1) (hb : d282284 q = 1) : d286269 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29006, d286269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29006, d286269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23534 q = 1) (hb : d282284 q = 1) : d286270 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d286270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d286270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
  have h15 (q : Pattern) (ha : d23422 q = 1) (hb : d282284 q = 1) : d286179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
    | true =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23535 q = 1) (hb : d282284 q = 1) : d286271 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d286271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23535, d286271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23423 q = 1) (hb : d282284 q = 1) : d286180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23536 q = 1) (hb : d282284 q = 1) : d286272 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d286272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23536, d286272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23537 q = 1) (hb : d282284 q = 1) : d286273 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d286273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23537, d286273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23310 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
  have h21 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23311 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d23312 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23313 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23538 q = 1) (hb : d282284 q = 1) : d286274 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d286274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23538, d286274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29007 q = 1) (hb : d282284 q = 1) : d286275 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29007, d286275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29007, d286275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72205 (p : Pattern) (ha : d29009 p = 1) (hb : d282284 p = 1) : d286067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d282284 q = 1) : d286057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d282284 q = 1) : d286058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d282284 q = 1) : d286059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d282284 q = 1) : d286060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d282284 q = 1) : d285915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d285915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d282284 q = 1) : d285872 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72137 q ha hb
    | true =>
      simp only [d28751, d285872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d282284 q = 1) : d285916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d285916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d282284 q = 1) : d285873 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d285873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d282284 q = 1) : d285917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d285917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d282284 q = 1) : d285918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d285918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d282284 q = 1) : d286061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d286061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d286061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d29008 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29008, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29009 q = 1) (hb : d282284 q = 1) : d286067 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29009, d286067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29009, d286067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro72206 (p : Pattern) (ha : d29013 p = 1) (hb : d282284 p = 1) : d286279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d282284 q = 1) : d286062 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d286062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d282284 q = 1) : d285994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72133 q ha hb
    | true =>
      simp only [d23231, d285994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d282284 q = 1) : d286063 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d286063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d282284 q = 1) : d285995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d285995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d282284 q = 1) : d286064 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d286064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d282284 q = 1) : d286065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d286065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d282284 q = 1) : d257230 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d257230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d282284 q = 1) : d257189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72160 q ha hb
    | true =>
      simp only [d751, d257189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d282284 q = 1) : d257231 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d257231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d282284 q = 1) : d257190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d257190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d282284 q = 1) : d257232 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d257232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d282284 q = 1) : d257233 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d257233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29008 q = 1) (hb : d282284 q = 1) : d286066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29008, d286066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d282284 q = 1) : d257234 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d257234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29013 q = 1) (hb : d282284 q = 1) : d286279 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29013, d286279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29013, d286279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72207 (p : Pattern) (ha : d29023 p = 1) (hb : d282284 p = 1) : d286285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29010 q = 1) (hb : d282284 q = 1) : d286276 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29010, d286276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72204 q ha hb
    | true =>
      simp only [d29010, d286276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72205 q ha hb
  have h2 (q : Pattern) (ha : d29011 q = 1) (hb : d282284 q = 1) : d286277 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29011, d286277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29011, d286277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29012 q = 1) (hb : d282284 q = 1) : d286278 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29012, d286278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29012, d286278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29014 q = 1) (hb : d282284 q = 1) : d286280 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29014, d286280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72205 q ha hb
    | true =>
      simp only [d29014, d286280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72206 q ha hb
  have h5 (q : Pattern) (ha : d29015 q = 1) (hb : d282284 q = 1) : d286281 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29015, d286281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29015, d286281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29016 q = 1) (hb : d282284 q = 1) : d286282 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29016, d286282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29016, d286282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29017 q = 1) (hb : d282284 q = 1) : d286283 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29017, d286283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29017, d286283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29018 q = 1) (hb : d282284 q = 1) : d286068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72205 q ha hb
    | true =>
      simp only [d29018, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72168 q ha hb
  have h9 (q : Pattern) (ha : d29019 q = 1) (hb : d282284 q = 1) : d286069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29020 q = 1) (hb : d282284 q = 1) : d286070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72168 q ha hb
    | true =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72169 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29021 q = 1) (hb : d282284 q = 1) : d286071 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29021, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29022 q = 1) (hb : d282284 q = 1) : d286284 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29022, d286284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29022, d286284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29023 q = 1) (hb : d282284 q = 1) : d286285 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29023, d286285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29023, d286285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72208 (p : Pattern) (ha : d29027 p = 1) (hb : d282284 p = 1) : d286290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29018 q = 1) (hb : d282284 q = 1) : d286068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72205 q ha hb
    | true =>
      simp only [d29018, d286068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72168 q ha hb
  have h2 (q : Pattern) (ha : d29019 q = 1) (hb : d282284 q = 1) : d286069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d286069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29020 q = 1) (hb : d282284 q = 1) : d286070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d286070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d282284 q = 1) : d285921 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72168 q ha hb
    | true =>
      simp only [d987, d285921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72169 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d282284 q = 1) : d285922 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d285922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d282284 q = 1) : d285923 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d285923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29021 q = 1) (hb : d282284 q = 1) : d286071 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29021, d286071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d282284 q = 1) : d286288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d286288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29026 q = 1) (hb : d282284 q = 1) : d286289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29026, d286289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29026, d286289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29027 q = 1) (hb : d282284 q = 1) : d286290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29027, d286290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29027, d286290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72209 (p : Pattern) (ha : d29033 p = 1) (hb : d282284 p = 1) : d286296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29024 q = 1) (hb : d282284 q = 1) : d286286 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29024, d286286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72207 q ha hb
    | true =>
      simp only [d29024, d286286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29025 q = 1) (hb : d282284 q = 1) : d286287 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29025, d286287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29025, d286287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29028 q = 1) (hb : d282284 q = 1) : d286291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72208 q ha hb
    | true =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29029 q = 1) (hb : d282284 q = 1) : d286292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29030 q = 1) (hb : d282284 q = 1) : d286293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29030, d286293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29030, d286293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29031 q = 1) (hb : d282284 q = 1) : d286294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29031, d286294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29031, d286294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29032 q = 1) (hb : d282284 q = 1) : d286295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29032, d286295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29032, d286295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29033 q = 1) (hb : d282284 q = 1) : d286296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29033, d286296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29033, d286296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72210 (p : Pattern) (ha : d29037 p = 1) (hb : d282284 p = 1) : d286304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d282284 q = 1) : d286291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72208 q ha hb
    | true =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d282284 q = 1) : d286292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d282284 q = 1) : d286299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72170 q ha hb
    | true =>
      simp only [d1006, d286299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d282284 q = 1) : d286300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d286300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29034 q = 1) (hb : d282284 q = 1) : d286301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29034, d286301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29034, d286301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29035 q = 1) (hb : d282284 q = 1) : d286302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29035, d286302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29035, d286302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29036 q = 1) (hb : d282284 q = 1) : d286303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29036, d286303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29036, d286303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29037 q = 1) (hb : d282284 q = 1) : d286304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29037, d286304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29037, d286304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72211 (p : Pattern) (ha : d29067 p = 1) (hb : d282284 p = 1) : d286310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d282284 q = 1) : d286291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72208 q ha hb
    | true =>
      simp only [d29028, d286291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d282284 q = 1) : d286292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d286292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29064 q = 1) (hb : d282284 q = 1) : d286307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29064, d286307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29064, d286307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29065 q = 1) (hb : d282284 q = 1) : d286308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29065, d286308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29065, d286308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29066 q = 1) (hb : d282284 q = 1) : d286309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29066, d286309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29066, d286309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29067 q = 1) (hb : d282284 q = 1) : d286310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29067, d286310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29067, d286310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72212 (p : Pattern) (ha : d238937 p = 1) (hb : d282284 p = 1) : d286316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29038 q = 1) (hb : d282284 q = 1) : d286305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29038, d286305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72209 q ha hb
    | true =>
      simp only [d29038, d286305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72210 q ha hb
  have h2 (q : Pattern) (ha : d238933 q = 1) (hb : d282284 q = 1) : d286306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238933, d286306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238933, d286306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29068 q = 1) (hb : d282284 q = 1) : d286311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29068, d286311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72211 q ha hb
    | true =>
      simp only [d29068, d286311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29069 q = 1) (hb : d282284 q = 1) : d286312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29069, d286312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29069, d286312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238934 q = 1) (hb : d282284 q = 1) : d286313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238934, d286313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238934, d286313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238935 q = 1) (hb : d282284 q = 1) : d286314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238935, d286314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238935, d286314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238936 q = 1) (hb : d282284 q = 1) : d286315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238936, d286315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238936, d286315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238937 q = 1) (hb : d282284 q = 1) : d286316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238937, d286316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238937, d286316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72213 (p : Pattern) (ha : d238943 p = 1) (hb : d282284 p = 1) : d286333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28855 q = 1) (hb : d282284 q = 1) : d286128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28855, d286128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28855, d286128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72176 q ha hb
  have h2 (q : Pattern) (ha : d28856 q = 1) (hb : d282284 q = 1) : d286129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28856, d286129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28856, d286129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28864 q = 1) (hb : d282284 q = 1) : d286138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, d286138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72176 q ha hb
    | true =>
      simp only [d28864, d286138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72178 q ha hb
  have h4 (q : Pattern) (ha : d28865 q = 1) (hb : d282284 q = 1) : d286139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, d286139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28865, d286139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28866 q = 1) (hb : d282284 q = 1) : d286140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d28866, d286140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28866, d286140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238921 q = 1) (hb : d282284 q = 1) : d286234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238921, d286234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72195 q ha hb
    | true =>
      simp only [d238921, d286234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72202 q ha hb
  have h7 (q : Pattern) (ha : d28986 q = 1) (hb : d282284 q = 1) : d286247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28986, d286247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72179 q ha hb
    | true =>
      simp only [d28986, d286247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72166 q ha hb
  have h8 (q : Pattern) (ha : d238922 q = 1) (hb : d282284 q = 1) : d286248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238922, d286248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238922, d286248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238923 q = 1) (hb : d282284 q = 1) : d286249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238923, d286249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238923, d286249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238924 q = 1) (hb : d282284 q = 1) : d286250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238924, d286250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238924, d286250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238928 q = 1) (hb : d282284 q = 1) : d286254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238928, d286254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238928, d286254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72203 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d282284 q = 1) : d286256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d286256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d286256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72167 q ha hb
  have h13 (q : Pattern) (ha : d238929 q = 1) (hb : d282284 q = 1) : d286257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238929, d286257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238929, d286257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238930 q = 1) (hb : d282284 q = 1) : d286258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238930, d286258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238930, d286258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238931 q = 1) (hb : d282284 q = 1) : d286259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238931, d286259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238931, d286259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238932 q = 1) (hb : d282284 q = 1) : d286260 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238932, d286260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238932, d286260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238938 q = 1) (hb : d282284 q = 1) : d286317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238938, d286317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238938, d286317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72212 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d282284 q = 1) : d286328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d286328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d286328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72172 q ha hb
  have h19 (q : Pattern) (ha : d238939 q = 1) (hb : d282284 q = 1) : d286329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238939, d286329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238939, d286329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238940 q = 1) (hb : d282284 q = 1) : d286330 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238940, d286330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238940, d286330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238941 q = 1) (hb : d282284 q = 1) : d286331 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238941, d286331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238941, d286331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238942 q = 1) (hb : d282284 q = 1) : d286332 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238942, d286332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238942, d286332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238943 q = 1) (hb : d282284 q = 1) : d286333 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238943, d286333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238943, d286333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro72214 (p : Pattern) (ha : d238949 p = 1) (hb : d282284 p = 1) : d286339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238944 q = 1) (hb : d282284 q = 1) : d286334 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238944, d286334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238944, d286334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72213 q ha hb
  have h2 (q : Pattern) (ha : d238945 q = 1) (hb : d282284 q = 1) : d286335 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238945, d286335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238945, d286335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238946 q = 1) (hb : d282284 q = 1) : d286336 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238946, d286336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238946, d286336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238947 q = 1) (hb : d282284 q = 1) : d286337 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238947, d286337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238947, d286337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238948 q = 1) (hb : d282284 q = 1) : d286338 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238948, d286338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238948, d286338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238949 q = 1) (hb : d282284 q = 1) : d286339 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238949, d286339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238949, d286339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72215 (p : Pattern) (ha : d29093 p = 1) (hb : d282284 p = 1) : d286342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9796, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d29088 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29088, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29088, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29089 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29089, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29089, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d29090 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d29091 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29092 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d29093 q = 1) (hb : d282284 q = 1) : d286342 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29093, d286342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29093, d286342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro72216 (p : Pattern) (ha : d29099 p = 1) (hb : d282284 p = 1) : d286348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d282284 q = 1) : d286166 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72188 q ha hb
    | true =>
      simp only [d28892, d286166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d282284 q = 1) : d286167 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d286167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d282284 q = 1) : d286168 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d286168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d286168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d282284 q = 1) : d286169 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d286169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d286169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d282284 q = 1) : d286171 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72189 q ha hb
    | true =>
      simp only [d28897, d286171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d282284 q = 1) : d286172 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d286172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d282284 q = 1) : d286173 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d286173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d286173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d282284 q = 1) : d286174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d286174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d286174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d282284 q = 1) : d286175 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d286175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d286175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d282284 q = 1) : d286179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
    | true =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d282284 q = 1) : d286180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d282284 q = 1) : d286181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d282284 q = 1) : d286182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29094 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72215 q ha hb
    | true =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29095 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29096 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29097 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29098 q = 1) (hb : d282284 q = 1) : d286347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d286347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29098, d286347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29099 q = 1) (hb : d282284 q = 1) : d286348 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29099, d286348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29099, d286348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72217 (p : Pattern) (ha : d29100 p = 1) (hb : d282284 p = 1) : d286342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d282284 q = 1) : d257183 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72067 q ha hb
    | true =>
      simp only [d133, d282284, d257183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d282284 q = 1) : d257184 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d257184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d282284 q = 1) : d285868 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d285868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d135 q = 1) (hb : d282284 q = 1) : d257185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d257185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316 q = 1) (hb : d282284 q = 1) : d285869 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d285869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d282284 q = 1) : d285870 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d317, d285870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d29090 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h13 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d29091 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29092 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d29100 q = 1) (hb : d282284 q = 1) : d286342 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29100, d286342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29100, d286342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro72218 (p : Pattern) (ha : d29107 p = 1) (hb : d282284 p = 1) : d286351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d282284 q = 1) : d285988 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d285988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d282284 q = 1) : d285989 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d285989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29101 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
    | true =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29102 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29103 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29104 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29105 q = 1) (hb : d282284 q = 1) : d286349 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29105, d286349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29105, d286349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29094 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72215 q ha hb
    | true =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29095 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29096 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29097 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29106 q = 1) (hb : d282284 q = 1) : d286350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29106, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29107 q = 1) (hb : d282284 q = 1) : d286351 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29107, d286351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29107, d286351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72219 (p : Pattern) (ha : d29114 p = 1) (hb : d282284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72050 q ha hb
    | true =>
      simp only [d19, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29112 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29113 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29114 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro72220 (p : Pattern) (ha : d29120 p = 1) (hb : d282284 p = 1) : d286355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
    | true =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d282284 q = 1) : d286350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29115 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72219 q ha hb
    | true =>
      simp only [d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29116 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29117 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29118 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29119 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29120 q = 1) (hb : d282284 q = 1) : d286355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29120, d286355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29120, d286355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72221 (p : Pattern) (ha : d29127 p = 1) (hb : d282284 p = 1) : d286362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29108 q = 1) (hb : d282284 q = 1) : d286352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d286352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72216 q ha hb
    | true =>
      simp only [d29108, d286352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72218 q ha hb
  have h2 (q : Pattern) (ha : d29109 q = 1) (hb : d282284 q = 1) : d286353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d286353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d286353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29110 q = 1) (hb : d282284 q = 1) : d286354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d286354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d286354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29121 q = 1) (hb : d282284 q = 1) : d286356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72218 q ha hb
    | true =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72220 q ha hb
  have h5 (q : Pattern) (ha : d29122 q = 1) (hb : d282284 q = 1) : d286357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29123 q = 1) (hb : d282284 q = 1) : d286358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29124 q = 1) (hb : d282284 q = 1) : d286359 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d286359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29124, d286359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29125 q = 1) (hb : d282284 q = 1) : d286360 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d286360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29125, d286360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29126 q = 1) (hb : d282284 q = 1) : d286361 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29126, d286361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29126, d286361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29127 q = 1) (hb : d282284 q = 1) : d286362 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29127, d286362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29127, d286362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro72222 (p : Pattern) (ha : d29131 p = 1) (hb : d282284 p = 1) : d286366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29121 q = 1) (hb : d282284 q = 1) : d286356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72218 q ha hb
    | true =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72220 q ha hb
  have h2 (q : Pattern) (ha : d29122 q = 1) (hb : d282284 q = 1) : d286357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29123 q = 1) (hb : d282284 q = 1) : d286358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29125 q = 1) (hb : d282284 q = 1) : d286360 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d286360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29125, d286360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29130 q = 1) (hb : d282284 q = 1) : d286365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29130, d286365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29130, d286365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29131 q = 1) (hb : d282284 q = 1) : d286366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29131, d286366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29131, d286366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72223 (p : Pattern) (ha : d29137 p = 1) (hb : d282284 p = 1) : d286372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d282284 q = 1) : d286363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72221 q ha hb
    | true =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d282284 q = 1) : d286364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d282284 q = 1) : d286369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d282284 q = 1) : d286370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d282284 q = 1) : d286371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d286371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d286371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29137 q = 1) (hb : d282284 q = 1) : d286372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29137, d286372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29137, d286372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72224 (p : Pattern) (ha : d29141 p = 1) (hb : d282284 p = 1) : d286376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d282284 q = 1) : d286373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d282284 q = 1) : d286374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d282284 q = 1) : d286375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d286375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d286375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29141 q = 1) (hb : d282284 q = 1) : d286376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29141, d286376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29141, d286376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72225 (p : Pattern) (ha : d29147 p = 1) (hb : d282284 p = 1) : d286382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d282284 q = 1) : d286377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72223 q ha hb
    | true =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72224 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d282284 q = 1) : d286378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d282284 q = 1) : d286379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d282284 q = 1) : d286380 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d282284 q = 1) : d286381 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29147 q = 1) (hb : d282284 q = 1) : d286382 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29147, d286382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29147, d286382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72226 (p : Pattern) (ha : d29150 p = 1) (hb : d282284 p = 1) : d286385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d282284 q = 1) : d286363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72221 q ha hb
    | true =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d282284 q = 1) : d286364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d282284 q = 1) : d286369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d282284 q = 1) : d286370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d282284 q = 1) : d286371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d286371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d286371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29150 q = 1) (hb : d282284 q = 1) : d286385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29150, d286385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29150, d286385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro72227 (p : Pattern) (ha : d29151 p = 1) (hb : d282284 p = 1) : d286386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d282284 q = 1) : d286373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d282284 q = 1) : d286374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d282284 q = 1) : d286375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d286375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d286375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29151 q = 1) (hb : d282284 q = 1) : d286386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29151, d286386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29151, d286386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72228 (p : Pattern) (ha : d29157 p = 1) (hb : d282284 p = 1) : d286392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d282284 q = 1) : d286377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72223 q ha hb
    | true =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72224 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d282284 q = 1) : d286378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d282284 q = 1) : d286379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d282284 q = 1) : d286380 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d282284 q = 1) : d286381 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29152 q = 1) (hb : d282284 q = 1) : d286387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29152, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72226 q ha hb
    | true =>
      simp only [d29152, d286387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72227 q ha hb
  have h7 (q : Pattern) (ha : d29153 q = 1) (hb : d282284 q = 1) : d286388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29153, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29153, d286388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29154 q = 1) (hb : d282284 q = 1) : d286389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29154, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29154, d286389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29155 q = 1) (hb : d282284 q = 1) : d286390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29155, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29155, d286390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29156 q = 1) (hb : d282284 q = 1) : d286391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29156, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29156, d286391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29157 q = 1) (hb : d282284 q = 1) : d286392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29157, d286392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29157, d286392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72229 (p : Pattern) (ha : d29339 p = 1) (hb : d282284 p = 1) : d286491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d282284 q = 1) : d286377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72223 q ha hb
    | true =>
      simp only [d29142, d286377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72224 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d282284 q = 1) : d286378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d286378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d282284 q = 1) : d286379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d286379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d282284 q = 1) : d286380 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d286380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d282284 q = 1) : d286381 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d286381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29334 q = 1) (hb : d282284 q = 1) : d286486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d286486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72224 q ha hb
    | true =>
      simp only [d29334, d286486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29335 q = 1) (hb : d282284 q = 1) : d286487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d286487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d286487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29336 q = 1) (hb : d282284 q = 1) : d286488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d286488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29336, d286488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29337 q = 1) (hb : d282284 q = 1) : d286489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d286489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d286489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29338 q = 1) (hb : d282284 q = 1) : d286490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d286490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d286490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29339 q = 1) (hb : d282284 q = 1) : d286491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29339, d286491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29339, d286491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72230 (p : Pattern) (ha : d29345 p = 1) (hb : d282284 p = 1) : d286497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29334 q = 1) (hb : d282284 q = 1) : d286486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d286486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72224 q ha hb
    | true =>
      simp only [d29334, d286486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29335 q = 1) (hb : d282284 q = 1) : d286487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d286487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d286487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29336 q = 1) (hb : d282284 q = 1) : d286488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d286488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29336, d286488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29337 q = 1) (hb : d282284 q = 1) : d286489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d286489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d286489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29338 q = 1) (hb : d282284 q = 1) : d286490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d286490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d286490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29340 q = 1) (hb : d282284 q = 1) : d286492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d286492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72227 q ha hb
    | true =>
      simp only [d29340, d286492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29341 q = 1) (hb : d282284 q = 1) : d286493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d286493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d286493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29342 q = 1) (hb : d282284 q = 1) : d286494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d286494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29342, d286494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29343 q = 1) (hb : d282284 q = 1) : d286495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d286495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d286495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29344 q = 1) (hb : d282284 q = 1) : d286496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d286496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d286496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29345 q = 1) (hb : d282284 q = 1) : d286497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29345, d286497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29345, d286497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72231 (p : Pattern) (ha : d29354 p = 1) (hb : d282284 p = 1) : d286506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29340 q = 1) (hb : d282284 q = 1) : d286492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d286492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72227 q ha hb
    | true =>
      simp only [d29340, d286492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29341 q = 1) (hb : d282284 q = 1) : d286493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d286493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d286493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29342 q = 1) (hb : d282284 q = 1) : d286494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d286494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29342, d286494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29343 q = 1) (hb : d282284 q = 1) : d286495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d286495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d286495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29344 q = 1) (hb : d282284 q = 1) : d286496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d286496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d286496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29354 q = 1) (hb : d282284 q = 1) : d286506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29354, d286506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29354, d286506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72232 (p : Pattern) (ha : d29390 p = 1) (hb : d282284 p = 1) : d286543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d282284 q = 1) : d286057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d286057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d282284 q = 1) : d285986 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72136 q ha hb
    | true =>
      simp only [d28746, d285986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d282284 q = 1) : d286058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d286058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d282284 q = 1) : d285987 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d285987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d282284 q = 1) : d286059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d286059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d282284 q = 1) : d286060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d286060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29385 q = 1) (hb : d282284 q = 1) : d286527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
  have h8 (q : Pattern) (ha : d29101 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
    | true =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29386 q = 1) (hb : d282284 q = 1) : d286528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29386, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29102 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29387 q = 1) (hb : d282284 q = 1) : d286529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29387, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29388 q = 1) (hb : d282284 q = 1) : d286530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29388, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29389 q = 1) (hb : d282284 q = 1) : d286542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29389, d286542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29389, d286542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29370 q = 1) (hb : d282284 q = 1) : d286527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29370, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29370, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72215 q ha hb
  have h15 (q : Pattern) (ha : d29094 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72215 q ha hb
    | true =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29371 q = 1) (hb : d282284 q = 1) : d286528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29371, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29371, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29095 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29372 q = 1) (hb : d282284 q = 1) : d286529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29372, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29372, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29373 q = 1) (hb : d282284 q = 1) : d286530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29373, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29373, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d29379 q = 1) (hb : d282284 q = 1) : d286536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29379, d286536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29379, d286536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d29390 q = 1) (hb : d282284 q = 1) : d286543 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29390, d286543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29390, d286543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro72233 (p : Pattern) (ha : d29400 p = 1) (hb : d282284 p = 1) : d286547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29385 q = 1) (hb : d282284 q = 1) : d286527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d286527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
  have h2 (q : Pattern) (ha : d29101 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
    | true =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29386 q = 1) (hb : d282284 q = 1) : d286528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29386, d286528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29102 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29387 q = 1) (hb : d282284 q = 1) : d286529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29387, d286529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29388 q = 1) (hb : d282284 q = 1) : d286530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29388, d286530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29394 q = 1) (hb : d282284 q = 1) : d286536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29394, d286536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29394, d286536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29395 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72219 q ha hb
  have h9 (q : Pattern) (ha : d29115 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72219 q ha hb
    | true =>
      simp only [d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29396 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29116 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29397 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29398 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29399 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29400 q = 1) (hb : d282284 q = 1) : d286547 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29400, d286547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29400, d286547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro72234 (p : Pattern) (ha : d29419 p = 1) (hb : d282284 p = 1) : d286566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29401 q = 1) (hb : d282284 q = 1) : d286548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29401, d286548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72232 q ha hb
    | true =>
      simp only [d29401, d286548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72233 q ha hb
  have h2 (q : Pattern) (ha : d29402 q = 1) (hb : d282284 q = 1) : d286549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29402, d286549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29402, d286549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29403 q = 1) (hb : d282284 q = 1) : d286550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29403, d286550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29403, d286550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29409 q = 1) (hb : d282284 q = 1) : d286556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29409, d286556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29409, d286556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29418 q = 1) (hb : d282284 q = 1) : d286565 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29418, d286565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29418, d286565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29419 q = 1) (hb : d282284 q = 1) : d286566 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29419, d286566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29419, d286566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72235 (p : Pattern) (ha : d29505 p = 1) (hb : d282284 p = 1) : d286589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29420 q = 1) (hb : d282284 q = 1) : d286567 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29420, d286567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72234 q ha hb
    | true =>
      simp only [d29420, d286567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29421 q = 1) (hb : d282284 q = 1) : d286568 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29421, d286568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29421, d286568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29502 q = 1) (hb : d282284 q = 1) : d286586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29502, d286586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29502, d286586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29503 q = 1) (hb : d282284 q = 1) : d286587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29503, d286587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29503, d286587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29504 q = 1) (hb : d282284 q = 1) : d286588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29504, d286588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29504, d286588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29505 q = 1) (hb : d282284 q = 1) : d286589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29505, d286589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29505, d286589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro72236 (p : Pattern) (ha : d29511 p = 1) (hb : d282284 p = 1) : d286595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29506 q = 1) (hb : d282284 q = 1) : d286590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29506, d286590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72235 q ha hb
    | true =>
      simp only [d29506, d286590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29507 q = 1) (hb : d282284 q = 1) : d286591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29507, d286591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29507, d286591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29508 q = 1) (hb : d282284 q = 1) : d286592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29508, d286592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29508, d286592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29509 q = 1) (hb : d282284 q = 1) : d286593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29509, d286593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29509, d286593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29510 q = 1) (hb : d282284 q = 1) : d286594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29510, d286594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29510, d286594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29511 q = 1) (hb : d282284 q = 1) : d286595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29511, d286595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29511, d286595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72237 (p : Pattern) (ha : d29162 p = 1) (hb : d282284 p = 1) : d286397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d282284 q = 1) : d286363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72221 q ha hb
    | true =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d282284 q = 1) : d286364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d282284 q = 1) : d286369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d282284 q = 1) : d286370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d286370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29161 q = 1) (hb : d282284 q = 1) : d286396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29161, d286396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29161, d286396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29162 q = 1) (hb : d282284 q = 1) : d286397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29162, d286397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29162, d286397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72238 (p : Pattern) (ha : d29164 p = 1) (hb : d282284 p = 1) : d286399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d282284 q = 1) : d286373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d282284 q = 1) : d286374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d286374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29163 q = 1) (hb : d282284 q = 1) : d286398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29163, d286398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29163, d286398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29164 q = 1) (hb : d282284 q = 1) : d286399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29164, d286399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29164, d286399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72239 (p : Pattern) (ha : d29171 p = 1) (hb : d282284 p = 1) : d286406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d282284 q = 1) : d286363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72221 q ha hb
    | true =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d282284 q = 1) : d286364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d282284 q = 1) : d286369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d286369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29169 q = 1) (hb : d282284 q = 1) : d286404 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29169, d286404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29169, d286404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29170 q = 1) (hb : d282284 q = 1) : d286405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29170, d286405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29170, d286405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29171 q = 1) (hb : d282284 q = 1) : d286406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29171, d286406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29171, d286406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72240 (p : Pattern) (ha : d29174 p = 1) (hb : d282284 p = 1) : d286409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d282284 q = 1) : d286367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72222 q ha hb
    | true =>
      simp only [d29132, d286367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d282284 q = 1) : d286368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d286368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d282284 q = 1) : d286373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d286373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29172 q = 1) (hb : d282284 q = 1) : d286407 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29172, d286407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29172, d286407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29173 q = 1) (hb : d282284 q = 1) : d286408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29173, d286408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29173, d286408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29174 q = 1) (hb : d282284 q = 1) : d286409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29174, d286409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29174, d286409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro72241 (p : Pattern) (ha : d23694 p = 1) (hb : d282284 p = 1) : d286429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d282284 q = 1) : d286159 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72185 q ha hb
    | true =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d282284 q = 1) : d286160 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d282284 q = 1) : d286161 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23692 q = 1) (hb : d282284 q = 1) : d286427 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d286427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23692, d286427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23693 q = 1) (hb : d282284 q = 1) : d286428 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d286428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23693, d286428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23419 q = 1) (hb : d282284 q = 1) : d286176 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d23420 q = 1) (hb : d282284 q = 1) : d286177 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d23694 q = 1) (hb : d282284 q = 1) : d286429 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d286429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23694, d286429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro72242 (p : Pattern) (ha : d1199 p = 1) (hb : d282283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d820 q = 1) (hb : d261984 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, d261984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d820, d261984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1199 q = 1) (hb : d282283 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1199, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1199, d282283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro72243 (p : Pattern) (ha : d29181 p = 1) (hb : d282284 p = 1) : d286416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72242 q ha hb
    | true =>
      simp only [d1200, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d822 q = 1) (hb : d282284 q = 1) : d286159 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72185 q ha hb
    | true =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d823 q = 1) (hb : d282284 q = 1) : d286160 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1202 q = 1) (hb : d282284 q = 1) : d286413 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d286413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1202, d286413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24014 q = 1) (hb : d282284 q = 1) : d286414 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24014, d286414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24014, d286414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d24015 q = 1) (hb : d282284 q = 1) : d286415 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24015, d286415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24015, d286415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d824 q = 1) (hb : d282284 q = 1) : d286161 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28883 q = 1) (hb : d282284 q = 1) : d258107 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72187 q ha hb
    | true =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28884 q = 1) (hb : d282284 q = 1) : d258108 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d29178 q = 1) (hb : d282284 q = 1) : d286162 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29178, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29178, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29179 q = 1) (hb : d282284 q = 1) : d286163 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29179, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29179, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29180 q = 1) (hb : d282284 q = 1) : d286164 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29180, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29180, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d29181 q = 1) (hb : d282284 q = 1) : d286416 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29181, d286416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29181, d286416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro72244 (p : Pattern) (ha : d29186 p = 1) (hb : d282284 p = 1) : d286421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d282284 q = 1) : d286159 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72185 q ha hb
    | true =>
      simp only [d822, d282284, d286159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d282284 q = 1) : d286160 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d286160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d282284 q = 1) : d285979 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72134 q ha hb
    | true =>
      simp only [d531, d282284, d285979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d282284 q = 1) : d285980 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d285980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d282284 q = 1) : d286161 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d286161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28880 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72186 q ha hb
    | true =>
      simp only [d28880, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28881 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d28883 q = 1) (hb : d282284 q = 1) : d258107 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72187 q ha hb
    | true =>
      simp only [d28883, d282284, d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28884 q = 1) (hb : d282284 q = 1) : d258108 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28884, d258108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28885 q = 1) (hb : d282284 q = 1) : d286162 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28885, d286162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28886 q = 1) (hb : d282284 q = 1) : d286163 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28886, d286163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28887 q = 1) (hb : d282284 q = 1) : d286164 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28887, d286164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d313 q = 1) (hb : d282284 q = 1) : d285866 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72093 q ha hb
    | true =>
      simp only [d313, d282284, d285866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d314 q = 1) (hb : d282284 q = 1) : d285867 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d314, d285867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d533 q = 1) (hb : d282284 q = 1) : d285981 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d285981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23419 q = 1) (hb : d282284 q = 1) : d286176 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23419, d286176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d23420 q = 1) (hb : d282284 q = 1) : d286177 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d23420, d286177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d29186 q = 1) (hb : d282284 q = 1) : d286421 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29186, d286421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29186, d286421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72245 (p : Pattern) (ha : d29192 p = 1) (hb : d282284 p = 1) : d286435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29182 q = 1) (hb : d282284 q = 1) : d286417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29182, d286417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72243 q ha hb
    | true =>
      simp only [d29182, d286417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29183 q = 1) (hb : d282284 q = 1) : d286418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29183, d286418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29183, d286418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29184 q = 1) (hb : d282284 q = 1) : d286419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29184, d286419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29184, d286419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29185 q = 1) (hb : d282284 q = 1) : d286420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29185, d286420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29185, d286420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29187 q = 1) (hb : d282284 q = 1) : d286422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29187, d286422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72244 q ha hb
    | true =>
      simp only [d29187, d286422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29188 q = 1) (hb : d282284 q = 1) : d286423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29188, d286423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29188, d286423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29189 q = 1) (hb : d282284 q = 1) : d286424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29189, d286424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29189, d286424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29190 q = 1) (hb : d282284 q = 1) : d286425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29190, d286425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29190, d286425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29191 q = 1) (hb : d282284 q = 1) : d286426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29191, d286426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29191, d286426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23695 q = 1) (hb : d282284 q = 1) : d286430 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d286430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72241 q ha hb
    | true =>
      simp only [d23695, d286430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23696 q = 1) (hb : d282284 q = 1) : d286431 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d286431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23696, d286431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23697 q = 1) (hb : d282284 q = 1) : d286432 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d286432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d286432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23698 q = 1) (hb : d282284 q = 1) : d286433 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d286433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23698, d286433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23422 q = 1) (hb : d282284 q = 1) : d286179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
    | true =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23423 q = 1) (hb : d282284 q = 1) : d286180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23424 q = 1) (hb : d282284 q = 1) : d286181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23425 q = 1) (hb : d282284 q = 1) : d286182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23699 q = 1) (hb : d282284 q = 1) : d286434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d286434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23699, d286434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29192 q = 1) (hb : d282284 q = 1) : d286435 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29192, d286435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29192, d286435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro72246 (p : Pattern) (ha : d29196 p = 1) (hb : d282284 p = 1) : d286439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d282284 q = 1) : d286179 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72184 q ha hb
    | true =>
      simp only [d23422, d286179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d282284 q = 1) : d286180 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d286180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d282284 q = 1) : d286181 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d286181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d282284 q = 1) : d286182 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d286182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29094 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72215 q ha hb
    | true =>
      simp only [d29094, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29095 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29095, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29096 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29097 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29097, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29098 q = 1) (hb : d282284 q = 1) : d286347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d286347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29098, d286347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29106 q = 1) (hb : d282284 q = 1) : d286350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29106, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29196 q = 1) (hb : d282284 q = 1) : d286439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29196, d286439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29196, d286439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro72247 (p : Pattern) (ha : d29202 p = 1) (hb : d282284 p = 1) : d286445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29193 q = 1) (hb : d282284 q = 1) : d286436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29193, d286436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72245 q ha hb
    | true =>
      simp only [d29193, d286436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72216 q ha hb
  have h2 (q : Pattern) (ha : d29194 q = 1) (hb : d282284 q = 1) : d286437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29194, d286437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29194, d286437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29195 q = 1) (hb : d282284 q = 1) : d286438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29195, d286438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29195, d286438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29197 q = 1) (hb : d282284 q = 1) : d286440 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29197, d286440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72216 q ha hb
    | true =>
      simp only [d29197, d286440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72246 q ha hb
  have h5 (q : Pattern) (ha : d29198 q = 1) (hb : d282284 q = 1) : d286441 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29198, d286441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29198, d286441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29199 q = 1) (hb : d282284 q = 1) : d286442 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29199, d286442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29199, d286442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29200 q = 1) (hb : d282284 q = 1) : d286443 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29200, d286443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29200, d286443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29108 q = 1) (hb : d282284 q = 1) : d286352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d286352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72216 q ha hb
    | true =>
      simp only [d29108, d286352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72218 q ha hb
  have h9 (q : Pattern) (ha : d29109 q = 1) (hb : d282284 q = 1) : d286353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d286353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d286353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29110 q = 1) (hb : d282284 q = 1) : d286354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d286354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d286354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29121 q = 1) (hb : d282284 q = 1) : d286356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72218 q ha hb
    | true =>
      simp only [d29121, d286356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72220 q ha hb
  have h12 (q : Pattern) (ha : d29122 q = 1) (hb : d282284 q = 1) : d286357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d286357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29123 q = 1) (hb : d282284 q = 1) : d286358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d286358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29124 q = 1) (hb : d282284 q = 1) : d286359 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d286359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29124, d286359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29201 q = 1) (hb : d282284 q = 1) : d286444 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29201, d286444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29201, d286444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29202 q = 1) (hb : d282284 q = 1) : d286445 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29202, d286445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29202, d286445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro72248 (p : Pattern) (ha : d29208 p = 1) (hb : d282284 p = 1) : d286451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29203 q = 1) (hb : d282284 q = 1) : d286446 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29203, d286446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72247 q ha hb
    | true =>
      simp only [d29203, d286446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29204 q = 1) (hb : d282284 q = 1) : d286447 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29204, d286447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29204, d286447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29128 q = 1) (hb : d282284 q = 1) : d286363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72221 q ha hb
    | true =>
      simp only [d29128, d286363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29129 q = 1) (hb : d282284 q = 1) : d286364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d286364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29205 q = 1) (hb : d282284 q = 1) : d286448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29205, d286448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29205, d286448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29206 q = 1) (hb : d282284 q = 1) : d286449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29206, d286449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29206, d286449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29207 q = 1) (hb : d282284 q = 1) : d286450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29207, d286450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29207, d286450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29208 q = 1) (hb : d282284 q = 1) : d286451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29208, d286451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29208, d286451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro72249 (p : Pattern) (ha : d29290 p = 1) (hb : d282284 p = 1) : d286355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d282284 q = 1) : d286343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72217 q ha hb
    | true =>
      simp only [d29101, d286343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d282284 q = 1) : d286344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d286344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d282284 q = 1) : d286345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d286345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d282284 q = 1) : d286346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d286346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d282284 q = 1) : d286350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d286350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29290 q = 1) (hb : d282284 q = 1) : d286355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29290, d286355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29290, d286355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
