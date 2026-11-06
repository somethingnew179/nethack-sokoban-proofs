import NetHack.Soko22Hazard87.EqIntroBlocks0092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro23250 (p : Pattern) (selected : d232645 p = 0) : d234233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232616 q = 0) : d234207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232616, d234207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23240 q selected
    | true =>
      simp only [d232616, d234207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232617 q = 0) : d234208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232617, d234208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232617, d234208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232618 q = 0) : d234209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232618, d234209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232618, d234209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232619 q = 0) : d234210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232619, d234210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232619, d234210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232620 q = 0) : d234211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232620, d234211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232620, d234211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232645 q = 0) : d234233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232645, d234233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232645, d234233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23251 (p : Pattern) (selected : d232651 p = 0) : d234239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232516 q = 0) : d234157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232516, d234157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23219 q selected
    | true =>
      simp only [d232516, d234157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23220 q selected
  have h2 (q : Pattern) (selected : d232517 q = 0) : d234158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232517, d234158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232517, d234158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232518 q = 0) : d234159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232518, d234159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232518, d234159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232519 q = 0) : d234160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232519, d234160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232519, d234160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232526 q = 0) : d234167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232526, d234167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23221 q selected
    | true =>
      simp only [d232526, d234167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23222 q selected
  have h6 (q : Pattern) (selected : d232527 q = 0) : d234168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232527, d234168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232527, d234168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232528 q = 0) : d234169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232528, d234169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232528, d234169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232549 q = 0) : d234190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232549, d234190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23226 q selected
    | true =>
      simp only [d232549, d234190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23213 q selected
  have h9 (q : Pattern) (selected : d232599 q = 0) : d234134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232599, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23235 q selected
    | true =>
      simp only [d232599, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23236 q selected
  have h10 (q : Pattern) (selected : d232600 q = 0) : d234191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232600, d234191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232600, d234191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232622 q = 0) : d234213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232622, d234213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23241 q selected
    | true =>
      simp only [d232622, d234213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232623 q = 0) : d234214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232623, d234214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232623, d234214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232624 q = 0) : d234215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232624, d234215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232624, d234215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232625 q = 0) : d234216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232625, d234216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232625, d234216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232626 q = 0) : d234217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232626, d234217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232626, d234217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232630 q = 0) : d234221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232630, d234221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23243 q selected
    | true =>
      simp only [d232630, d234221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23244 q selected
  have h17 (q : Pattern) (selected : d232631 q = 0) : d234222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232631, d234222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232631, d234222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d232632 q = 0) : d234223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232632, d234223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232632, d234223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d232633 q = 0) : d234224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232633, d234224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232633, d234224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d232636 q = 0) : d234227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232636, d234227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23245 q selected
    | true =>
      simp only [d232636, d234227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23246 q selected
  have h21 (q : Pattern) (selected : d232637 q = 0) : d234228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232637, d234228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232637, d234228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d232638 q = 0) : d234229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232638, d234229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d232638, d234229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d232640 q = 0) : d234231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232640, d234231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23247 q selected
    | true =>
      simp only [d232640, d234231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23216 q selected
  have h24 (q : Pattern) (selected : d232643 q = 0) : d234144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232643, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23248 q selected
    | true =>
      simp only [d232643, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23249 q selected
  have h25 (q : Pattern) (selected : d232644 q = 0) : d234232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232644, d234232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d232644, d234232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d232646 q = 0) : d234234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232646, d234234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23250 q selected
    | true =>
      simp only [d232646, d234234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d232647 q = 0) : d234235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232647, d234235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d232647, d234235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d232648 q = 0) : d234236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232648, d234236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d232648, d234236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d232649 q = 0) : d234237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232649, d234237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d232649, d234237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d232650 q = 0) : d234238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232650, d234238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232650, d234238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d232651 q = 0) : d234239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232651, d234239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232651, d234239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23252 (p : Pattern) (selected : d232658 p = 0) : d234246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232493 q = 0) : d234134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23213 q selected
    | true =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23214 q selected
  have h2 (q : Pattern) (selected : d232494 q = 0) : d234135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232495 q = 0) : d234136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232496 q = 0) : d234137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232497 q = 0) : d234138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232653 q = 0) : d234241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232653, d234241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23214 q selected
    | true =>
      simp only [d232653, d234241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232654 q = 0) : d234242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232654, d234242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232654, d234242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232655 q = 0) : d234243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232655, d234243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232655, d234243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232656 q = 0) : d234244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232656, d234244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232656, d234244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232657 q = 0) : d234245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232657, d234245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232657, d234245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232658 q = 0) : d234246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232658, d234246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232658, d234246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23253 (p : Pattern) (selected : d232664 p = 0) : d234252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232653 q = 0) : d234241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232653, d234241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23214 q selected
    | true =>
      simp only [d232653, d234241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232654 q = 0) : d234242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232654, d234242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232654, d234242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232655 q = 0) : d234243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232655, d234243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232655, d234243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232656 q = 0) : d234244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232656, d234244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232656, d234244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232657 q = 0) : d234245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232657, d234245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232657, d234245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232659 q = 0) : d234247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232659, d234247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23217 q selected
    | true =>
      simp only [d232659, d234247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232660 q = 0) : d234248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232660, d234248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232660, d234248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232661 q = 0) : d234249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232661, d234249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232661, d234249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232662 q = 0) : d234250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232662, d234250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232662, d234250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232663 q = 0) : d234251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232663, d234251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232663, d234251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232664 q = 0) : d234252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232664, d234252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232664, d234252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23254 (p : Pattern) (selected : d232671 p = 0) : d234259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232640 q = 0) : d234231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232640, d234231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23247 q selected
    | true =>
      simp only [d232640, d234231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23216 q selected
  have h2 (q : Pattern) (selected : d232643 q = 0) : d234144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232643, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23248 q selected
    | true =>
      simp only [d232643, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23249 q selected
  have h3 (q : Pattern) (selected : d232644 q = 0) : d234232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232644, d234232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232644, d234232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232646 q = 0) : d234234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232646, d234234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23250 q selected
    | true =>
      simp only [d232646, d234234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232647 q = 0) : d234235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232647, d234235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232647, d234235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232648 q = 0) : d234236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232648, d234236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232648, d234236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232669 q = 0) : d234257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232669, d234257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232669, d234257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232670 q = 0) : d234258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232670, d234258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232670, d234258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232671 q = 0) : d234259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232671, d234259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232671, d234259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23255 (p : Pattern) (selected : d232673 p = 0) : d234261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232659 q = 0) : d234247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232659, d234247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23217 q selected
    | true =>
      simp only [d232659, d234247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232660 q = 0) : d234248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232660, d234248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232660, d234248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232661 q = 0) : d234249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232661, d234249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232661, d234249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232662 q = 0) : d234250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232662, d234250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232662, d234250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232663 q = 0) : d234251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232663, d234251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232663, d234251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232673 q = 0) : d234261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232673, d234261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232673, d234261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23256 (p : Pattern) (selected : d232693 p = 0) : d234281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232679 q = 0) : d234267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232679, d234267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232679, d234267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23223 q selected
  have h2 (q : Pattern) (selected : d232531 q = 0) : d234172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232531, d234172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23223 q selected
    | true =>
      simp only [d232531, d234172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232680 q = 0) : d234268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232680, d234268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232680, d234268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232532 q = 0) : d234173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232532, d234173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232532, d234173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232681 q = 0) : d234269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232681, d234269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232681, d234269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232682 q = 0) : d234270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232682, d234270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232682, d234270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232683 q = 0) : d234271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232683, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232683, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
  have h8 (q : Pattern) (selected : d232447 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
    | true =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232684 q = 0) : d234272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232684, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232684, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232448 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232685 q = 0) : d234273 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232685, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232685, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232686 q = 0) : d234274 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232686, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232686, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232687 q = 0) : d234275 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232687, d234275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232687, d234275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232688 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
  have h15 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232689 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232690 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232691 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232692 q = 0) : d234280 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232692, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232692, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232693 q = 0) : d234281 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232693, d234281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232693, d234281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23257 (p : Pattern) (selected : d232699 p = 0) : d234287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232683 q = 0) : d234271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232683, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232683, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
  have h2 (q : Pattern) (selected : d232447 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
    | true =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232684 q = 0) : d234272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232684, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232684, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232448 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232685 q = 0) : d234273 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232685, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232685, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232686 q = 0) : d234274 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232686, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232686, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232688 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
  have h8 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232689 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232690 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232691 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232692 q = 0) : d234280 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232692, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232692, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232694 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
  have h15 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232695 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232696 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232697 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232698 q = 0) : d234286 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232699 q = 0) : d234287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232699, d234287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232699, d234287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23258 (p : Pattern) (selected : d232704 p = 0) : d234292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232688 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
  have h2 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232689 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232690 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232691 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232694 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
  have h8 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232695 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232696 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232697 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232698 q = 0) : d234286 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232703 q = 0) : d234291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232703, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232703, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232704 q = 0) : d234292 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232704, d234292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232704, d234292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23259 (p : Pattern) (selected : d232709 p = 0) : d234297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232694 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
  have h2 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232695 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232696 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232697 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232703 q = 0) : d234291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232703, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232703, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232709 q = 0) : d234297 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232709, d234297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232709, d234297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23260 (p : Pattern) (selected : d232715 p = 0) : d234303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232700 q = 0) : d234288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232700, d234288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23256 q selected
    | true =>
      simp only [d232700, d234288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23257 q selected
  have h2 (q : Pattern) (selected : d232701 q = 0) : d234289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232701, d234289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232701, d234289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232702 q = 0) : d234290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232702, d234290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232702, d234290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232705 q = 0) : d234293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23257 q selected
    | true =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
  have h5 (q : Pattern) (selected : d232706 q = 0) : d234294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232707 q = 0) : d234295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232708 q = 0) : d234296 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232708, d234296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232708, d234296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232710 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
    | true =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23259 q selected
  have h9 (q : Pattern) (selected : d232711 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232712 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232713 q = 0) : d234301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232714 q = 0) : d234302 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232714, d234302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232714, d234302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232715 q = 0) : d234303 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232715, d234303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232715, d234303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23261 (p : Pattern) (selected : d232720 p = 0) : d234308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232705 q = 0) : d234293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23257 q selected
    | true =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
  have h2 (q : Pattern) (selected : d232706 q = 0) : d234294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232707 q = 0) : d234295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232710 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
    | true =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23259 q selected
  have h5 (q : Pattern) (selected : d232711 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232712 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232713 q = 0) : d234301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232718 q = 0) : d234306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232718, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232718, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232719 q = 0) : d234307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232719, d234307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232719, d234307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232720 q = 0) : d234308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232720, d234308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232720, d234308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23262 (p : Pattern) (selected : d232726 p = 0) : d234314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232716 q = 0) : d234304 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232716, d234304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23260 q selected
    | true =>
      simp only [d232716, d234304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232717 q = 0) : d234305 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232717, d234305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232717, d234305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232721 q = 0) : d234309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232721, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23261 q selected
    | true =>
      simp only [d232721, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232722 q = 0) : d234310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232722, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232722, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232723 q = 0) : d234311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232723, d234311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232723, d234311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232724 q = 0) : d234312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232724, d234312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232724, d234312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232725 q = 0) : d234313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232725, d234313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232725, d234313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232726 q = 0) : d234314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232726, d234314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232726, d234314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23263 (p : Pattern) (selected : d232728 p = 0) : d234316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232710 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
    | true =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23259 q selected
  have h2 (q : Pattern) (selected : d232711 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232712 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232718 q = 0) : d234306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232718, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232718, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232727 q = 0) : d234315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232727, d234315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232727, d234315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232728 q = 0) : d234316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232728, d234316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232728, d234316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23264 (p : Pattern) (selected : d232734 p = 0) : d234322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232721 q = 0) : d234309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232721, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23261 q selected
    | true =>
      simp only [d232721, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232722 q = 0) : d234310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232722, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232722, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232729 q = 0) : d234317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232729, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23263 q selected
    | true =>
      simp only [d232729, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232730 q = 0) : d234318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232730, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232730, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232731 q = 0) : d234319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232731, d234319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232731, d234319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232732 q = 0) : d234320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232732, d234320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232732, d234320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232733 q = 0) : d234321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232733, d234321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232733, d234321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232734 q = 0) : d234322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232734, d234322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232734, d234322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23265 (p : Pattern) (selected : d232750 p = 0) : d234287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232736 q = 0) : d234271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232736, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232736, d234271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23227 q selected
  have h2 (q : Pattern) (selected : d232553 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232553, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23227 q selected
    | true =>
      simp only [d232553, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232737 q = 0) : d234272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232737, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232737, d234272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232554 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232554, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232554, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232738 q = 0) : d234273 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232738, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232738, d234273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232739 q = 0) : d234274 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232739, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232739, d234274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232740 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232740, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232740, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
  have h8 (q : Pattern) (selected : d232559 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
    | true =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232741 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232741, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232741, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232560 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232742 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232742, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232742, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232743 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232743, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232743, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232744 q = 0) : d234280 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232744, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232744, d234280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232745 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
  have h15 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232746 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232747 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232748 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232749 q = 0) : d234286 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232749, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232749, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232750 q = 0) : d234287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232750, d234287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232750, d234287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23266 (p : Pattern) (selected : d232752 p = 0) : d234292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232740 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232740, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232740, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
  have h2 (q : Pattern) (selected : d232559 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
    | true =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232741 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232741, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232741, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232560 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232742 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232742, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232742, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232743 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232743, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232743, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232745 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
  have h8 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232746 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232747 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232748 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232749 q = 0) : d234286 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232749, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232749, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232751 q = 0) : d234291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232751, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232751, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232752 q = 0) : d234292 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232752, d234292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232752, d234292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23267 (p : Pattern) (selected : d232756 p = 0) : d234297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232745 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
  have h2 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232746 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232746, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232747 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232747, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232748 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232748, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232751 q = 0) : d234291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232751, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232751, d234291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232756 q = 0) : d234297 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232756, d234297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232756, d234297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23268 (p : Pattern) (selected : d232763 p = 0) : d234308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232753 q = 0) : d234293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232753, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23265 q selected
    | true =>
      simp only [d232753, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23266 q selected
  have h2 (q : Pattern) (selected : d232754 q = 0) : d234294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232754, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232754, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232755 q = 0) : d234295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232755, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232755, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232757 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232757, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23266 q selected
    | true =>
      simp only [d232757, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23267 q selected
  have h5 (q : Pattern) (selected : d232758 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232758, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232758, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232759 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232759, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232759, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232760 q = 0) : d234301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232760, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232760, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232761 q = 0) : d234306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232761, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232761, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232762 q = 0) : d234307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232762, d234307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232762, d234307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232763 q = 0) : d234308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232763, d234308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232763, d234308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23269 (p : Pattern) (selected : d232767 p = 0) : d234316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232757 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232757, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23266 q selected
    | true =>
      simp only [d232757, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23267 q selected
  have h2 (q : Pattern) (selected : d232758 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232758, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232758, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232759 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232759, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232759, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232761 q = 0) : d234306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232761, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232761, d234306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232766 q = 0) : d234315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232766, d234315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232766, d234315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232767 q = 0) : d234316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232767, d234316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232767, d234316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23270 (p : Pattern) (selected : d232773 p = 0) : d234322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232764 q = 0) : d234309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232764, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23268 q selected
    | true =>
      simp only [d232764, d234309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232765 q = 0) : d234310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232765, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232765, d234310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232768 q = 0) : d234317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232768, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23269 q selected
    | true =>
      simp only [d232768, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232769 q = 0) : d234318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232769, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232769, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232770 q = 0) : d234319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232770, d234319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232770, d234319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232771 q = 0) : d234320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232771, d234320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232771, d234320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232772 q = 0) : d234321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232772, d234321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232772, d234321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232773 q = 0) : d234322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232773, d234322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232773, d234322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23271 (p : Pattern) (selected : d232777 p = 0) : d234327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232768 q = 0) : d234317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232768, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23269 q selected
    | true =>
      simp only [d232768, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232769 q = 0) : d234318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232769, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232769, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232774 q = 0) : d234324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232774, d234324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232774, d234324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232775 q = 0) : d234325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232775, d234325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232775, d234325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232776 q = 0) : d234326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232776, d234326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232776, d234326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232777 q = 0) : d234327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232777, d234327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232777, d234327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23272 (p : Pattern) (selected : d232785 p = 0) : d234335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232688 q = 0) : d234276 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232688, d234276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
  have h2 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232689 q = 0) : d234277 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232689, d234277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232690 q = 0) : d234278 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232690, d234278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232691 q = 0) : d234279 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232691, d234279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232694 q = 0) : d234282 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232694, d234282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
  have h8 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232695 q = 0) : d234283 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232695, d234283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232696 q = 0) : d234284 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232696, d234284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232697 q = 0) : d234285 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232697, d234285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232698 q = 0) : d234286 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232698, d234286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232780 q = 0) : d234330 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232780, d234330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232780, d234330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
  have h15 (q : Pattern) (selected : d232603 q = 0) : d234194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
    | true =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232781 q = 0) : d234331 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232781, d234331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232781, d234331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232604 q = 0) : d234195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232782 q = 0) : d234332 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232782, d234332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232782, d234332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232783 q = 0) : d234333 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232783, d234333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232783, d234333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232784 q = 0) : d234334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232784, d234334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232784, d234334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d232785 q = 0) : d234335 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232785, d234335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232785, d234335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23273 (p : Pattern) (selected : d232786 p = 0) : d234336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232780 q = 0) : d234330 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232780, d234330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232780, d234330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
  have h2 (q : Pattern) (selected : d232603 q = 0) : d234194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
    | true =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232781 q = 0) : d234331 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232781, d234331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232781, d234331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232604 q = 0) : d234195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232782 q = 0) : d234332 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232782, d234332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232782, d234332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232783 q = 0) : d234333 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232783, d234333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232783, d234333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232784 q = 0) : d234334 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232784, d234334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232784, d234334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232786 q = 0) : d234336 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232786, d234336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232786, d234336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23274 (p : Pattern) (selected : d232792 p = 0) : d234342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232705 q = 0) : d234293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23257 q selected
    | true =>
      simp only [d232705, d234293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
  have h2 (q : Pattern) (selected : d232706 q = 0) : d234294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232706, d234294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232707 q = 0) : d234295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232707, d234295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232710 q = 0) : d234298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23258 q selected
    | true =>
      simp only [d232710, d234298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23259 q selected
  have h5 (q : Pattern) (selected : d232711 q = 0) : d234299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232711, d234299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232712 q = 0) : d234300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232712, d234300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232713 q = 0) : d234301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232713, d234301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232787 q = 0) : d234337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232787, d234337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23272 q selected
    | true =>
      simp only [d232787, d234337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23273 q selected
  have h9 (q : Pattern) (selected : d232788 q = 0) : d234338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232788, d234338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232788, d234338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232789 q = 0) : d234339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232789, d234339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232789, d234339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232790 q = 0) : d234340 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232790, d234340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232790, d234340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232791 q = 0) : d234341 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232791, d234341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232791, d234341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232792 q = 0) : d234342 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232792, d234342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232792, d234342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23275 (p : Pattern) (selected : d232798 p = 0) : d234348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232793 q = 0) : d234343 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232793, d234343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23274 q selected
    | true =>
      simp only [d232793, d234343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232794 q = 0) : d234344 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232794, d234344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232794, d234344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232795 q = 0) : d234345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232795, d234345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232795, d234345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232796 q = 0) : d234346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232796, d234346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232796, d234346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232797 q = 0) : d234347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232797, d234347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232797, d234347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232798 q = 0) : d234348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232798, d234348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232798, d234348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23276 (p : Pattern) (selected : d232804 p = 0) : d234354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232735 q = 0) : d234323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232735, d234323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23262 q selected
    | true =>
      simp only [d232735, d234323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23264 q selected
  have h2 (q : Pattern) (selected : d232778 q = 0) : d234328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232778, d234328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23270 q selected
    | true =>
      simp only [d232778, d234328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23271 q selected
  have h3 (q : Pattern) (selected : d232779 q = 0) : d234329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232779, d234329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232779, d234329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232799 q = 0) : d234349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232799, d234349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23275 q selected
    | true =>
      simp only [d232799, d234349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232800 q = 0) : d234350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232800, d234350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232800, d234350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232801 q = 0) : d234351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232801, d234351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232801, d234351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232802 q = 0) : d234352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232802, d234352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232802, d234352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232803 q = 0) : d234353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232803, d234353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232803, d234353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232804 q = 0) : d234354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232804, d234354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232804, d234354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23277 (p : Pattern) (selected : d232809 p = 0) : d234327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232729 q = 0) : d234317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232729, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23263 q selected
    | true =>
      simp only [d232729, d234317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232730 q = 0) : d234318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232730, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232730, d234318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232806 q = 0) : d234324 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232806, d234324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232806, d234324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232807 q = 0) : d234325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232807, d234325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232807, d234325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232808 q = 0) : d234326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232808, d234326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232808, d234326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232809 q = 0) : d234327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232809, d234327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232809, d234327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23278 (p : Pattern) (selected : d232815 p = 0) : d234361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232810 q = 0) : d234356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232810, d234356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23277 q selected
    | true =>
      simp only [d232810, d234356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232811 q = 0) : d234357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232811, d234357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232811, d234357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232812 q = 0) : d234358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232812, d234358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232812, d234358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232813 q = 0) : d234359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232813, d234359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232813, d234359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232814 q = 0) : d234360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232814, d234360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232814, d234360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232815 q = 0) : d234361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232815, d234361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232815, d234361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23279 (p : Pattern) (selected : d232821 p = 0) : d234367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232499 q = 0) : d234140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232499, d234140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232499, d234140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23215 q selected
  have h2 (q : Pattern) (selected : d232500 q = 0) : d234141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232500, d234141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232500, d234141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232509 q = 0) : d234150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232509, d234150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23215 q selected
    | true =>
      simp only [d232509, d234150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23218 q selected
  have h4 (q : Pattern) (selected : d232510 q = 0) : d234151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232510, d234151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232510, d234151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232511 q = 0) : d234152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232511, d234152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232511, d234152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232652 q = 0) : d234240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232652, d234240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23242 q selected
    | true =>
      simp only [d232652, d234240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23251 q selected
  have h7 (q : Pattern) (selected : d232665 q = 0) : d234253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232665, d234253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23252 q selected
    | true =>
      simp only [d232665, d234253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23253 q selected
  have h8 (q : Pattern) (selected : d232666 q = 0) : d234254 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232666, d234254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232666, d234254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232667 q = 0) : d234255 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232667, d234255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232667, d234255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d232668 q = 0) : d234256 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232668, d234256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232668, d234256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232672 q = 0) : d234260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232672, d234260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232672, d234260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23254 q selected
  have h12 (q : Pattern) (selected : d232674 q = 0) : d234262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232674, d234262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232674, d234262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23255 q selected
  have h13 (q : Pattern) (selected : d232675 q = 0) : d234263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232675, d234263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232675, d234263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232676 q = 0) : d234264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232676, d234264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232676, d234264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232677 q = 0) : d234265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232677, d234265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232677, d234265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232678 q = 0) : d234266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232678, d234266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232678, d234266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232805 q = 0) : d234355 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232805, d234355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232805, d234355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23276 q selected
  have h18 (q : Pattern) (selected : d232816 q = 0) : d234362 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232816, d234362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232816, d234362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23278 q selected
  have h19 (q : Pattern) (selected : d232817 q = 0) : d234363 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232817, d234363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232817, d234363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d232818 q = 0) : d234364 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232818, d234364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232818, d234364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d232819 q = 0) : d234365 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232819, d234365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d232819, d234365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d232820 q = 0) : d234366 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232820, d234366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d232820, d234366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d232821 q = 0) : d234367 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232821, d234367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232821, d234367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro23280 (p : Pattern) (selected : d232827 p = 0) : d234373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232822 q = 0) : d234368 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232822, d234368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232822, d234368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23279 q selected
  have h2 (q : Pattern) (selected : d232823 q = 0) : d234369 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232823, d234369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232823, d234369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232824 q = 0) : d234370 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232824, d234370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232824, d234370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232825 q = 0) : d234371 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232825, d234371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232825, d234371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232826 q = 0) : d234372 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232826, d234372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232826, d234372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232827 q = 0) : d234373 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232827, d234373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232827, d234373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23281 (p : Pattern) (selected : d232834 p = 0) : d234380 p = 1 := by
  have h0 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232832 q = 0) : d234378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232832, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232832, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h6 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h7 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232833 q = 0) : d234379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232833, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232833, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232834 q = 0) : d234380 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232834, d234380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232834, d234380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23282 (p : Pattern) (selected : d232840 p = 0) : d234386 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h3 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232833 q = 0) : d234379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232833, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232833, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2041 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro554 q selected
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h6 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h7 (q : Pattern) (selected : d2044 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232839 q = 0) : d234385 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232839, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232839, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232840 q = 0) : d234386 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232840, d234386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232840, d234386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23283 (p : Pattern) (selected : d232847 p = 0) : d234393 p = 1 := by
  have h0 (q : Pattern) (selected : d2041 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro554 q selected
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h3 (q : Pattern) (selected : d2044 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232839 q = 0) : d234385 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232839, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232839, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232846 q = 0) : d234392 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232846, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232846, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232847 q = 0) : d234393 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232847, d234393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232847, d234393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23284 (p : Pattern) (selected : d232853 p = 0) : d234399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232835 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
    | true =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232836 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232837 q = 0) : d234383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232837, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232837, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232838 q = 0) : d234384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232838, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232838, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232843 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232844 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232845 q = 0) : d234391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232845, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232845, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232850 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232851 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232852 q = 0) : d234398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232853 q = 0) : d234399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232853, d234399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232853, d234399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23285 (p : Pattern) (selected : d232855 p = 0) : d234401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232843 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232844 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232850 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232851 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232852 q = 0) : d234398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232854 q = 0) : d234400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232854, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232854, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232855 q = 0) : d234401 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232855, d234401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232855, d234401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23286 (p : Pattern) (selected : d232859 p = 0) : d234405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232850 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232851 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232854 q = 0) : d234400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232854, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232854, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232859 q = 0) : d234405 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232859, d234405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232859, d234405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23287 (p : Pattern) (selected : d232866 p = 0) : d234412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232856 q = 0) : d234402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23284 q selected
    | true =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
  have h2 (q : Pattern) (selected : d232857 q = 0) : d234403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232858 q = 0) : d234404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232860 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
    | true =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23286 q selected
  have h5 (q : Pattern) (selected : d232861 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232862 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232863 q = 0) : d234409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232864 q = 0) : d234410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232864, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232864, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232865 q = 0) : d234411 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232865, d234411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232865, d234411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232866 q = 0) : d234412 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232866, d234412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232866, d234412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23288 (p : Pattern) (selected : d232870 p = 0) : d234416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232860 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
    | true =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23286 q selected
  have h2 (q : Pattern) (selected : d232861 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232862 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232864 q = 0) : d234410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232864, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232864, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232869 q = 0) : d234415 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232869, d234415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232869, d234415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232870 q = 0) : d234416 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232870, d234416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232870, d234416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23289 (p : Pattern) (selected : d232876 p = 0) : d234422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232874 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232875 q = 0) : d234421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232875, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232875, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232876 q = 0) : d234422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232876, d234422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232876, d234422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23290 (p : Pattern) (selected : d232880 p = 0) : d234426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232878 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232879 q = 0) : d234425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232879, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232879, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232880 q = 0) : d234426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232880, d234426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232880, d234426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23291 (p : Pattern) (selected : d232886 p = 0) : d234432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232881 q = 0) : d234427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23289 q selected
    | true =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23290 q selected
  have h2 (q : Pattern) (selected : d232882 q = 0) : d234428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232883 q = 0) : d234429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232884 q = 0) : d234430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232885 q = 0) : d234431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232886 q = 0) : d234432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232886, d234432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232886, d234432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23292 (p : Pattern) (selected : d232889 p = 0) : d234435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232874 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232875 q = 0) : d234421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232875, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232875, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232889 q = 0) : d234435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232889, d234435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232889, d234435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23293 (p : Pattern) (selected : d232890 p = 0) : d234436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232878 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232879 q = 0) : d234425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232879, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232879, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232890 q = 0) : d234436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232890, d234436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232890, d234436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23294 (p : Pattern) (selected : d232896 p = 0) : d234442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232881 q = 0) : d234427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23289 q selected
    | true =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23290 q selected
  have h2 (q : Pattern) (selected : d232882 q = 0) : d234428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232883 q = 0) : d234429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232884 q = 0) : d234430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232885 q = 0) : d234431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232891 q = 0) : d234437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232891, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23292 q selected
    | true =>
      simp only [d232891, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23293 q selected
  have h7 (q : Pattern) (selected : d232892 q = 0) : d234438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232892, d234438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232892, d234438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232893 q = 0) : d234439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232893, d234439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232893, d234439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232894 q = 0) : d234440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232894, d234440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232894, d234440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232895 q = 0) : d234441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232895, d234441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232895, d234441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232896 q = 0) : d234442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232896, d234442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232896, d234442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23295 (p : Pattern) (selected : d232901 p = 0) : d234447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232874 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232900 q = 0) : d234446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232900, d234446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232900, d234446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232901 q = 0) : d234447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232901, d234447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232901, d234447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23296 (p : Pattern) (selected : d232903 p = 0) : d234449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232878 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232902 q = 0) : d234448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232902, d234448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232902, d234448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232903 q = 0) : d234449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232903, d234449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232903, d234449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23297 (p : Pattern) (selected : d232910 p = 0) : d234456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232908 q = 0) : d234454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232908, d234454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232908, d234454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232909 q = 0) : d234455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232909, d234455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232909, d234455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232910 q = 0) : d234456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232910, d234456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232910, d234456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23298 (p : Pattern) (selected : d232913 p = 0) : d234459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232911 q = 0) : d234457 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232911, d234457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232911, d234457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232912 q = 0) : d234458 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232912, d234458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232912, d234458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232913 q = 0) : d234459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232913, d234459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232913, d234459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23299 (p : Pattern) (selected : d232917 p = 0) : d234463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232832 q = 0) : d234378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232832, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232832, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232917 q = 0) : d234463 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232917, d234463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232917, d234463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro23300 (p : Pattern) (selected : d232923 p = 0) : d234469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232918 q = 0) : d234464 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232918, d234464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23299 q selected
    | true =>
      simp only [d232918, d234464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232919 q = 0) : d234465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232919, d234465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232919, d234465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232920 q = 0) : d234466 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232920, d234466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232920, d234466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232921 q = 0) : d234467 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232921, d234467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232921, d234467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232835 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
    | true =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232836 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232837 q = 0) : d234383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232837, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232837, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232838 q = 0) : d234384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232838, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232838, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232922 q = 0) : d234468 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232922, d234468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232922, d234468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232843 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232844 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232845 q = 0) : d234391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232845, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232845, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232923 q = 0) : d234469 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232923, d234469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232923, d234469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23301 (p : Pattern) (selected : d232929 p = 0) : d234475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232924 q = 0) : d234470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232924, d234470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23300 q selected
    | true =>
      simp only [d232924, d234470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23284 q selected
  have h2 (q : Pattern) (selected : d232925 q = 0) : d234471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232925, d234471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232925, d234471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232926 q = 0) : d234472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232926, d234472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232926, d234472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232856 q = 0) : d234402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23284 q selected
    | true =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
  have h5 (q : Pattern) (selected : d232857 q = 0) : d234403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232858 q = 0) : d234404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232927 q = 0) : d234473 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232927, d234473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232927, d234473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232860 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
    | true =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23286 q selected
  have h9 (q : Pattern) (selected : d232861 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232862 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232863 q = 0) : d234409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232928 q = 0) : d234474 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232928, d234474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232928, d234474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232929 q = 0) : d234475 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232929, d234475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232929, d234475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23302 (p : Pattern) (selected : d232935 p = 0) : d234481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232930 q = 0) : d234476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232930, d234476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23301 q selected
    | true =>
      simp only [d232930, d234476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232931 q = 0) : d234477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232931, d234477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232931, d234477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232932 q = 0) : d234478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232932, d234478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232932, d234478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232933 q = 0) : d234479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232933, d234479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232933, d234479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232934 q = 0) : d234480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232934, d234480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232934, d234480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232935 q = 0) : d234481 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232935, d234481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232935, d234481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23303 (p : Pattern) (selected : d232939 p = 0) : d234380 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro580 q selected
    | true =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro581 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2174 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro582 q selected
  have h3 (q : Pattern) (selected : d2175 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232937 q = 0) : d234378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232937, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232937, d234378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h6 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h7 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232938 q = 0) : d234379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232938, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232938, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232939 q = 0) : d234380 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232939, d234380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232939, d234380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23304 (p : Pattern) (selected : d232945 p = 0) : d234386 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h3 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232938 q = 0) : d234379 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232938, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232938, d234379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2207 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro588 q selected
    | true =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h6 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h7 (q : Pattern) (selected : d2210 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232944 q = 0) : d234385 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232944, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232944, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232945 q = 0) : d234386 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232945, d234386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232945, d234386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23305 (p : Pattern) (selected : d232952 p = 0) : d234393 p = 1 := by
  have h0 (q : Pattern) (selected : d2207 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro588 q selected
    | true =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h3 (q : Pattern) (selected : d2210 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232944 q = 0) : d234385 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232944, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232944, d234385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232951 q = 0) : d234392 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232951, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232951, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232952 q = 0) : d234393 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232952, d234393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232952, d234393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23306 (p : Pattern) (selected : d232958 p = 0) : d234399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232940 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232940, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23303 q selected
    | true =>
      simp only [d232940, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232941 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232941, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232941, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232942 q = 0) : d234383 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232942, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232942, d234383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232943 q = 0) : d234384 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232943, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232943, d234384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232946 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
    | true =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232947 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232948 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232948, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232948, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232949 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232949, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232949, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232950 q = 0) : d234391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232950, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232950, d234391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232955 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232956 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232957 q = 0) : d234398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232957, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232957, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232958 q = 0) : d234399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232958, d234399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232958, d234399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23307 (p : Pattern) (selected : d232960 p = 0) : d234401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232946 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
    | true =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232947 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232948 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232948, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232948, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232949 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232949, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232949, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232955 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232956 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232957 q = 0) : d234398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232957, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232957, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232959 q = 0) : d234400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232959, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232959, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232960 q = 0) : d234401 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232960, d234401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232960, d234401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23308 (p : Pattern) (selected : d232964 p = 0) : d234405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232955 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232956 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232956, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232959 q = 0) : d234400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232959, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232959, d234400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232964 q = 0) : d234405 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232964, d234405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232964, d234405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23309 (p : Pattern) (selected : d232971 p = 0) : d234412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232961 q = 0) : d234402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232961, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23306 q selected
    | true =>
      simp only [d232961, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23307 q selected
  have h2 (q : Pattern) (selected : d232962 q = 0) : d234403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232962, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232962, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232963 q = 0) : d234404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232963, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232963, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232965 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232965, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23307 q selected
    | true =>
      simp only [d232965, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23308 q selected
  have h5 (q : Pattern) (selected : d232966 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232966, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232966, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232967 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232967, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232967, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232968 q = 0) : d234409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232968, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232968, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232969 q = 0) : d234410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232969, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232969, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232970 q = 0) : d234411 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232970, d234411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232970, d234411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232971 q = 0) : d234412 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232971, d234412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232971, d234412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23310 (p : Pattern) (selected : d232975 p = 0) : d234416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232965 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232965, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23307 q selected
    | true =>
      simp only [d232965, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23308 q selected
  have h2 (q : Pattern) (selected : d232966 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232966, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232966, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232967 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232967, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232967, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232969 q = 0) : d234410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232969, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232969, d234410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232974 q = 0) : d234415 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232974, d234415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232974, d234415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232975 q = 0) : d234416 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232975, d234416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232975, d234416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23311 (p : Pattern) (selected : d232981 p = 0) : d234422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232972 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232972, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23309 q selected
    | true =>
      simp only [d232972, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232973 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232973, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232973, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232976 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23310 q selected
    | true =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232977 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232978 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232978, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232978, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232979 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232979, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232979, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232980 q = 0) : d234421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232980, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232980, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232981 q = 0) : d234422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232981, d234422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232981, d234422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23312 (p : Pattern) (selected : d232985 p = 0) : d234426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232976 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23310 q selected
    | true =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232977 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232982 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232982, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232982, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232983 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232983, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232983, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232984 q = 0) : d234425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232984, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232984, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232985 q = 0) : d234426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232985, d234426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232985, d234426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23313 (p : Pattern) (selected : d232988 p = 0) : d234484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232846 q = 0) : d234392 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232846, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232846, d234392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232988 q = 0) : d234484 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232988, d234484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232988, d234484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro23314 (p : Pattern) (selected : d232994 p = 0) : d234490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232843 q = 0) : d234389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232843, d234389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232844 q = 0) : d234390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232844, d234390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232850 q = 0) : d234396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232850, d234396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232851 q = 0) : d234397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232851, d234397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232852 q = 0) : d234398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232852, d234398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232989 q = 0) : d234485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
    | true =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232990 q = 0) : d234486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232991 q = 0) : d234487 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232991, d234487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232991, d234487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232992 q = 0) : d234488 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232992, d234488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232992, d234488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232993 q = 0) : d234489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232993, d234489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232993, d234489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232994 q = 0) : d234490 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232994, d234490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232994, d234490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23315 (p : Pattern) (selected : d232995 p = 0) : d234491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232989 q = 0) : d234485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
    | true =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232990 q = 0) : d234486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232991 q = 0) : d234487 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232991, d234487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232991, d234487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232992 q = 0) : d234488 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232992, d234488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232992, d234488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232993 q = 0) : d234489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232993, d234489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232993, d234489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232995 q = 0) : d234491 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232995, d234491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232995, d234491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23316 (p : Pattern) (selected : d233001 p = 0) : d234497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232856 q = 0) : d234402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23284 q selected
    | true =>
      simp only [d232856, d234402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
  have h2 (q : Pattern) (selected : d232857 q = 0) : d234403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232857, d234403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232858 q = 0) : d234404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232858, d234404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232860 q = 0) : d234406 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23285 q selected
    | true =>
      simp only [d232860, d234406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23286 q selected
  have h5 (q : Pattern) (selected : d232861 q = 0) : d234407 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232861, d234407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232862 q = 0) : d234408 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232862, d234408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232863 q = 0) : d234409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232863, d234409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232996 q = 0) : d234492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232996, d234492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23314 q selected
    | true =>
      simp only [d232996, d234492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23315 q selected
  have h9 (q : Pattern) (selected : d232997 q = 0) : d234493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232997, d234493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232997, d234493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232998 q = 0) : d234494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232998, d234494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232998, d234494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232999 q = 0) : d234495 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232999, d234495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232999, d234495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d233000 q = 0) : d234496 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233000, d234496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233000, d234496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233001 q = 0) : d234497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233001, d234497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233001, d234497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23317 (p : Pattern) (selected : d233007 p = 0) : d234503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233002 q = 0) : d234498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233002, d234498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23316 q selected
    | true =>
      simp only [d233002, d234498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233003 q = 0) : d234499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233003, d234499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233003, d234499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233004 q = 0) : d234500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233004, d234500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233004, d234500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233005 q = 0) : d234501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233005, d234501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233005, d234501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233006 q = 0) : d234502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233006, d234502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233006, d234502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233007 q = 0) : d234503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233007, d234503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233007, d234503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23318 (p : Pattern) (selected : d233013 p = 0) : d234509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232904 q = 0) : d234450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232904, d234450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23295 q selected
    | true =>
      simp only [d232904, d234450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23296 q selected
  have h2 (q : Pattern) (selected : d232905 q = 0) : d234451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232905, d234451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232905, d234451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232906 q = 0) : d234452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232906, d234452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232906, d234452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232907 q = 0) : d234453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232907, d234453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232907, d234453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232914 q = 0) : d234460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232914, d234460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23297 q selected
    | true =>
      simp only [d232914, d234460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23298 q selected
  have h6 (q : Pattern) (selected : d232915 q = 0) : d234461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232915, d234461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232915, d234461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232916 q = 0) : d234462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232916, d234462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232916, d234462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232936 q = 0) : d234482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232936, d234482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23302 q selected
    | true =>
      simp only [d232936, d234482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23289 q selected
  have h9 (q : Pattern) (selected : d232986 q = 0) : d234427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232986, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23311 q selected
    | true =>
      simp only [d232986, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23312 q selected
  have h10 (q : Pattern) (selected : d232987 q = 0) : d234483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232987, d234483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232987, d234483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233008 q = 0) : d234504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233008, d234504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23317 q selected
    | true =>
      simp only [d233008, d234504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d233009 q = 0) : d234505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233009, d234505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233009, d234505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233010 q = 0) : d234506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233010, d234506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233010, d234506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233011 q = 0) : d234507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233011, d234507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233011, d234507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d233012 q = 0) : d234508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233012, d234508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233012, d234508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233013 q = 0) : d234509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233013, d234509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233013, d234509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23319 (p : Pattern) (selected : d233014 p = 0) : d234510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232874 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232874, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232900 q = 0) : d234446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232900, d234446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232900, d234446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233014 q = 0) : d234510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233014, d234510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233014, d234510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23320 (p : Pattern) (selected : d233015 p = 0) : d234511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232878 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232878, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232902 q = 0) : d234448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232902, d234448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232902, d234448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233015 q = 0) : d234511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233015, d234511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233015, d234511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23321 (p : Pattern) (selected : d233020 p = 0) : d234516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232873 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232873, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232908 q = 0) : d234454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232908, d234454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232908, d234454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232909 q = 0) : d234455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232909, d234455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232909, d234455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233020 q = 0) : d234516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233020, d234516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233020, d234516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23322 (p : Pattern) (selected : d233021 p = 0) : d234517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232871 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23288 q selected
    | true =>
      simp only [d232871, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232872 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232872, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232877 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232877, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232911 q = 0) : d234457 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232911, d234457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232911, d234457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232912 q = 0) : d234458 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232912, d234458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232912, d234458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233021 q = 0) : d234517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233021, d234517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233021, d234517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23323 (p : Pattern) (selected : d233025 p = 0) : d234521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232930 q = 0) : d234476 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232930, d234476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23301 q selected
    | true =>
      simp only [d232930, d234476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232931 q = 0) : d234477 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232931, d234477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232931, d234477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232867 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23287 q selected
    | true =>
      simp only [d232867, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232868 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232868, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232932 q = 0) : d234478 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232932, d234478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232932, d234478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232933 q = 0) : d234479 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232933, d234479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232933, d234479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232934 q = 0) : d234480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232934, d234480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232934, d234480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233025 q = 0) : d234521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233025, d234521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233025, d234521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23324 (p : Pattern) (selected : d233027 p = 0) : d234435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232972 q = 0) : d234413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232972, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23309 q selected
    | true =>
      simp only [d232972, d234413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232973 q = 0) : d234414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232973, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232973, d234414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232976 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23310 q selected
    | true =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232977 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232978 q = 0) : d234419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232978, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232978, d234419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232979 q = 0) : d234420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232979, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232979, d234420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232980 q = 0) : d234421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232980, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232980, d234421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233027 q = 0) : d234435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233027, d234435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233027, d234435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23325 (p : Pattern) (selected : d233028 p = 0) : d234436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232976 q = 0) : d234417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23310 q selected
    | true =>
      simp only [d232976, d234417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232977 q = 0) : d234418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, d234418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232982 q = 0) : d234423 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232982, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232982, d234423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232983 q = 0) : d234424 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232983, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232983, d234424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232984 q = 0) : d234425 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232984, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232984, d234425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233028 q = 0) : d234436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233028, d234436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233028, d234436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23326 (p : Pattern) (selected : d233031 p = 0) : d234524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233002 q = 0) : d234498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233002, d234498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23316 q selected
    | true =>
      simp only [d233002, d234498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233003 q = 0) : d234499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233003, d234499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233003, d234499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233004 q = 0) : d234500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233004, d234500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233004, d234500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233005 q = 0) : d234501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233005, d234501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233005, d234501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233006 q = 0) : d234502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233006, d234502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233006, d234502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233031 q = 0) : d234524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233031, d234524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233031, d234524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23327 (p : Pattern) (selected : d233037 p = 0) : d234530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232904 q = 0) : d234450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232904, d234450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23295 q selected
    | true =>
      simp only [d232904, d234450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23296 q selected
  have h2 (q : Pattern) (selected : d232905 q = 0) : d234451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232905, d234451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232905, d234451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232906 q = 0) : d234452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232906, d234452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232906, d234452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232907 q = 0) : d234453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232907, d234453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232907, d234453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232914 q = 0) : d234460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232914, d234460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23297 q selected
    | true =>
      simp only [d232914, d234460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23298 q selected
  have h6 (q : Pattern) (selected : d232915 q = 0) : d234461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232915, d234461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232915, d234461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232916 q = 0) : d234462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232916, d234462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232916, d234462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232936 q = 0) : d234482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232936, d234482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23302 q selected
    | true =>
      simp only [d232936, d234482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23289 q selected
  have h9 (q : Pattern) (selected : d232986 q = 0) : d234427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232986, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23311 q selected
    | true =>
      simp only [d232986, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23312 q selected
  have h10 (q : Pattern) (selected : d232987 q = 0) : d234483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232987, d234483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232987, d234483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233008 q = 0) : d234504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233008, d234504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23317 q selected
    | true =>
      simp only [d233008, d234504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d233009 q = 0) : d234505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233009, d234505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233009, d234505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233010 q = 0) : d234506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233010, d234506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233010, d234506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233011 q = 0) : d234507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233011, d234507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233011, d234507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d233012 q = 0) : d234508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233012, d234508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233012, d234508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233016 q = 0) : d234512 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233016, d234512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23319 q selected
    | true =>
      simp only [d233016, d234512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23320 q selected
  have h17 (q : Pattern) (selected : d233017 q = 0) : d234513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233017, d234513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233017, d234513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d233018 q = 0) : d234514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233018, d234514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d233018, d234514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d233019 q = 0) : d234515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233019, d234515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233019, d234515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d233022 q = 0) : d234518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233022, d234518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23321 q selected
    | true =>
      simp only [d233022, d234518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23322 q selected
  have h21 (q : Pattern) (selected : d233023 q = 0) : d234519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233023, d234519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233023, d234519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d233024 q = 0) : d234520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233024, d234520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d233024, d234520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d233026 q = 0) : d234522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233026, d234522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23323 q selected
    | true =>
      simp only [d233026, d234522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23292 q selected
  have h24 (q : Pattern) (selected : d233029 q = 0) : d234437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233029, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23324 q selected
    | true =>
      simp only [d233029, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23325 q selected
  have h25 (q : Pattern) (selected : d233030 q = 0) : d234523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233030, d234523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d233030, d234523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d233032 q = 0) : d234525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233032, d234525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23326 q selected
    | true =>
      simp only [d233032, d234525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d233033 q = 0) : d234526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233033, d234526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d233033, d234526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d233034 q = 0) : d234527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233034, d234527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d233034, d234527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d233035 q = 0) : d234528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233035, d234528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d233035, d234528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d233036 q = 0) : d234529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233036, d234529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d233036, d234529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d233037 q = 0) : d234530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233037, d234530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d233037, d234530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23328 (p : Pattern) (selected : d233044 p = 0) : d234537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232881 q = 0) : d234427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23289 q selected
    | true =>
      simp only [d232881, d234427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23290 q selected
  have h2 (q : Pattern) (selected : d232882 q = 0) : d234428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232882, d234428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232883 q = 0) : d234429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232883, d234429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232884 q = 0) : d234430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232884, d234430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232885 q = 0) : d234431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232885, d234431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233039 q = 0) : d234532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233039, d234532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23290 q selected
    | true =>
      simp only [d233039, d234532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233040 q = 0) : d234533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233040, d234533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233040, d234533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233041 q = 0) : d234534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233041, d234534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233041, d234534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233042 q = 0) : d234535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233042, d234535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233042, d234535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233043 q = 0) : d234536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233043, d234536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233043, d234536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233044 q = 0) : d234537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233044, d234537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233044, d234537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23329 (p : Pattern) (selected : d233050 p = 0) : d234543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233039 q = 0) : d234532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233039, d234532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23290 q selected
    | true =>
      simp only [d233039, d234532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233040 q = 0) : d234533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233040, d234533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233040, d234533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233041 q = 0) : d234534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233041, d234534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233041, d234534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233042 q = 0) : d234535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233042, d234535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233042, d234535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233043 q = 0) : d234536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233043, d234536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233043, d234536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233045 q = 0) : d234538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233045, d234538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23293 q selected
    | true =>
      simp only [d233045, d234538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233046 q = 0) : d234539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233046, d234539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233046, d234539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233047 q = 0) : d234540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233047, d234540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233047, d234540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233048 q = 0) : d234541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233048, d234541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233048, d234541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233049 q = 0) : d234542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233049, d234542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233049, d234542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233050 q = 0) : d234543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233050, d234543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233050, d234543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23330 (p : Pattern) (selected : d233057 p = 0) : d234550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233026 q = 0) : d234522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233026, d234522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23323 q selected
    | true =>
      simp only [d233026, d234522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23292 q selected
  have h2 (q : Pattern) (selected : d233029 q = 0) : d234437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233029, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23324 q selected
    | true =>
      simp only [d233029, d234437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23325 q selected
  have h3 (q : Pattern) (selected : d233030 q = 0) : d234523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233030, d234523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233030, d234523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233032 q = 0) : d234525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233032, d234525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23326 q selected
    | true =>
      simp only [d233032, d234525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233033 q = 0) : d234526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233033, d234526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233033, d234526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233034 q = 0) : d234527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233034, d234527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233034, d234527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233055 q = 0) : d234548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233055, d234548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233055, d234548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233056 q = 0) : d234549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233056, d234549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233056, d234549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d233057 q = 0) : d234550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233057, d234550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233057, d234550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23331 (p : Pattern) (selected : d233059 p = 0) : d234552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233045 q = 0) : d234538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233045, d234538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23293 q selected
    | true =>
      simp only [d233045, d234538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233046 q = 0) : d234539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233046, d234539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233046, d234539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233047 q = 0) : d234540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233047, d234540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233047, d234540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233048 q = 0) : d234541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233048, d234541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233048, d234541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233049 q = 0) : d234542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233049, d234542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233049, d234542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233059 q = 0) : d234552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233059, d234552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233059, d234552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23332 (p : Pattern) (selected : d233079 p = 0) : d234572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233065 q = 0) : d234558 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233065, d234558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233065, d234558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23299 q selected
  have h2 (q : Pattern) (selected : d232918 q = 0) : d234464 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232918, d234464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23299 q selected
    | true =>
      simp only [d232918, d234464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233066 q = 0) : d234559 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233066, d234559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233066, d234559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232919 q = 0) : d234465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232919, d234465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232919, d234465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233067 q = 0) : d234560 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233067, d234560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233067, d234560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233068 q = 0) : d234561 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233068, d234561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233068, d234561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233069 q = 0) : d234562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233069, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233069, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
  have h8 (q : Pattern) (selected : d232835 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
    | true =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233070 q = 0) : d234563 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233070, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233070, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232836 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233071 q = 0) : d234564 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233071, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233071, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233072 q = 0) : d234565 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233072, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233072, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233073 q = 0) : d234566 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233073, d234566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233073, d234566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233074 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
  have h15 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233075 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d233076 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d233077 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d233078 q = 0) : d234571 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233078, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233078, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d233079 q = 0) : d234572 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233079, d234572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233079, d234572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23333 (p : Pattern) (selected : d233085 p = 0) : d234578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233069 q = 0) : d234562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233069, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233069, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
  have h2 (q : Pattern) (selected : d232835 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23281 q selected
    | true =>
      simp only [d232835, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233070 q = 0) : d234563 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233070, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233070, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232836 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232836, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233071 q = 0) : d234564 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233071, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233071, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233072 q = 0) : d234565 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233072, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233072, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233074 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
  have h8 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233075 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233076 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233077 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233078 q = 0) : d234571 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233078, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233078, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233080 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
  have h15 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233081 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d233082 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d233083 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d233084 q = 0) : d234577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d233085 q = 0) : d234578 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233085, d234578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233085, d234578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23334 (p : Pattern) (selected : d233090 p = 0) : d234583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233074 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
  have h2 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233075 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233076 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233077 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233080 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
  have h8 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233081 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233082 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233083 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233084 q = 0) : d234577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233089 q = 0) : d234582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233089, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233089, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d233090 q = 0) : d234583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233090, d234583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233090, d234583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23335 (p : Pattern) (selected : d233095 p = 0) : d234588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233080 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
  have h2 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233081 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233082 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233083 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233089 q = 0) : d234582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233089, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233089, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233095 q = 0) : d234588 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233095, d234588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233095, d234588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23336 (p : Pattern) (selected : d233101 p = 0) : d234594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233086 q = 0) : d234579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233086, d234579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23332 q selected
    | true =>
      simp only [d233086, d234579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23333 q selected
  have h2 (q : Pattern) (selected : d233087 q = 0) : d234580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233087, d234580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233087, d234580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233088 q = 0) : d234581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233088, d234581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233088, d234581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233091 q = 0) : d234584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23333 q selected
    | true =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
  have h5 (q : Pattern) (selected : d233092 q = 0) : d234585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233093 q = 0) : d234586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233094 q = 0) : d234587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233094, d234587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233094, d234587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233096 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
    | true =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23335 q selected
  have h9 (q : Pattern) (selected : d233097 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233098 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233099 q = 0) : d234592 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233100 q = 0) : d234593 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233100, d234593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233100, d234593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233101 q = 0) : d234594 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233101, d234594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233101, d234594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23337 (p : Pattern) (selected : d233106 p = 0) : d234599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233091 q = 0) : d234584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23333 q selected
    | true =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
  have h2 (q : Pattern) (selected : d233092 q = 0) : d234585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233093 q = 0) : d234586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233096 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
    | true =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23335 q selected
  have h5 (q : Pattern) (selected : d233097 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233098 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233099 q = 0) : d234592 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233104 q = 0) : d234597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233104, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233104, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233105 q = 0) : d234598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233105, d234598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233105, d234598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233106 q = 0) : d234599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233106, d234599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233106, d234599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23338 (p : Pattern) (selected : d233112 p = 0) : d234605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233102 q = 0) : d234595 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233102, d234595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23336 q selected
    | true =>
      simp only [d233102, d234595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233103 q = 0) : d234596 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233103, d234596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233103, d234596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233107 q = 0) : d234600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233107, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23337 q selected
    | true =>
      simp only [d233107, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233108 q = 0) : d234601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233108, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233108, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233109 q = 0) : d234602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233109, d234602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233109, d234602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233110 q = 0) : d234603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233110, d234603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233110, d234603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233111 q = 0) : d234604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233111, d234604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233111, d234604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233112 q = 0) : d234605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233112, d234605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233112, d234605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23339 (p : Pattern) (selected : d233114 p = 0) : d234607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233096 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
    | true =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23335 q selected
  have h2 (q : Pattern) (selected : d233097 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233098 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233104 q = 0) : d234597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233104, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233104, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233113 q = 0) : d234606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233113, d234606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233113, d234606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233114 q = 0) : d234607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233114, d234607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233114, d234607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23340 (p : Pattern) (selected : d233120 p = 0) : d234613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233107 q = 0) : d234600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233107, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23337 q selected
    | true =>
      simp only [d233107, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233108 q = 0) : d234601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233108, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233108, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233115 q = 0) : d234608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233115, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23339 q selected
    | true =>
      simp only [d233115, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233116 q = 0) : d234609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233116, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233116, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233117 q = 0) : d234610 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233117, d234610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233117, d234610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233118 q = 0) : d234611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233118, d234611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233118, d234611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233119 q = 0) : d234612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233119, d234612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233119, d234612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233120 q = 0) : d234613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233120, d234613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233120, d234613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23341 (p : Pattern) (selected : d233136 p = 0) : d234578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233122 q = 0) : d234562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233122, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233122, d234562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23303 q selected
  have h2 (q : Pattern) (selected : d232940 q = 0) : d234381 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232940, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23303 q selected
    | true =>
      simp only [d232940, d234381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233123 q = 0) : d234563 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233123, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233123, d234563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232941 q = 0) : d234382 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232941, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232941, d234382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233124 q = 0) : d234564 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233124, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233124, d234564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233125 q = 0) : d234565 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233125, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233125, d234565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233126 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233126, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233126, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
  have h8 (q : Pattern) (selected : d232946 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
    | true =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233127 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233127, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233127, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232947 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233128 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233128, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233128, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233129 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233129, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233129, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233130 q = 0) : d234571 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233130, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233130, d234571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233131 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
  have h15 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233132 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d233133 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d233134 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d233135 q = 0) : d234577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233135, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233135, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d233136 q = 0) : d234578 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233136, d234578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233136, d234578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23342 (p : Pattern) (selected : d233138 p = 0) : d234583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233126 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233126, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233126, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
  have h2 (q : Pattern) (selected : d232946 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23304 q selected
    | true =>
      simp only [d232946, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233127 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233127, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233127, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232947 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232947, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233128 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233128, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233128, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233129 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233129, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233129, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233131 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
  have h8 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233132 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233133 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233134 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233135 q = 0) : d234577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233135, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233135, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233137 q = 0) : d234582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233137, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233137, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d233138 q = 0) : d234583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233138, d234583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233138, d234583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23343 (p : Pattern) (selected : d233142 p = 0) : d234588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233131 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
  have h2 (q : Pattern) (selected : d232953 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23305 q selected
    | true =>
      simp only [d232953, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233132 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233132, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232954 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232954, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233133 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233133, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233134 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233134, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233137 q = 0) : d234582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233137, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233137, d234582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233142 q = 0) : d234588 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233142, d234588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233142, d234588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23344 (p : Pattern) (selected : d233149 p = 0) : d234599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233139 q = 0) : d234584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233139, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23341 q selected
    | true =>
      simp only [d233139, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23342 q selected
  have h2 (q : Pattern) (selected : d233140 q = 0) : d234585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233140, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233140, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233141 q = 0) : d234586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233141, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233141, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233143 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233143, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23342 q selected
    | true =>
      simp only [d233143, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23343 q selected
  have h5 (q : Pattern) (selected : d233144 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233144, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233144, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233145 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233145, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233145, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233146 q = 0) : d234592 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233146, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233146, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233147 q = 0) : d234597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233147, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233147, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233148 q = 0) : d234598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233148, d234598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233148, d234598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233149 q = 0) : d234599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233149, d234599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233149, d234599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23345 (p : Pattern) (selected : d233153 p = 0) : d234607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233143 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233143, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23342 q selected
    | true =>
      simp only [d233143, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23343 q selected
  have h2 (q : Pattern) (selected : d233144 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233144, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233144, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233145 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233145, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233145, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233147 q = 0) : d234597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233147, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233147, d234597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233152 q = 0) : d234606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233152, d234606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233152, d234606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233153 q = 0) : d234607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233153, d234607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233153, d234607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23346 (p : Pattern) (selected : d233159 p = 0) : d234613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233150 q = 0) : d234600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233150, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23344 q selected
    | true =>
      simp only [d233150, d234600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233151 q = 0) : d234601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233151, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233151, d234601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233154 q = 0) : d234608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233154, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23345 q selected
    | true =>
      simp only [d233154, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233155 q = 0) : d234609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233155, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233155, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233156 q = 0) : d234610 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233156, d234610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233156, d234610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233157 q = 0) : d234611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233157, d234611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233157, d234611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233158 q = 0) : d234612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233158, d234612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233158, d234612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233159 q = 0) : d234613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233159, d234613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233159, d234613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23347 (p : Pattern) (selected : d233163 p = 0) : d234618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233154 q = 0) : d234608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233154, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23345 q selected
    | true =>
      simp only [d233154, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233155 q = 0) : d234609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233155, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233155, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233160 q = 0) : d234615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233160, d234615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233160, d234615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233161 q = 0) : d234616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233161, d234616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233161, d234616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233162 q = 0) : d234617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233162, d234617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233162, d234617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233163 q = 0) : d234618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233163, d234618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233163, d234618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23348 (p : Pattern) (selected : d233171 p = 0) : d234626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233074 q = 0) : d234567 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233074, d234567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
  have h2 (q : Pattern) (selected : d232841 q = 0) : d234387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23282 q selected
    | true =>
      simp only [d232841, d234387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233075 q = 0) : d234568 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233075, d234568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232842 q = 0) : d234388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232842, d234388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233076 q = 0) : d234569 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233076, d234569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233077 q = 0) : d234570 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233077, d234570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233080 q = 0) : d234573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233080, d234573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
  have h8 (q : Pattern) (selected : d232848 q = 0) : d234394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23283 q selected
    | true =>
      simp only [d232848, d234394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233081 q = 0) : d234574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233081, d234574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232849 q = 0) : d234395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232849, d234395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233082 q = 0) : d234575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233082, d234575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233083 q = 0) : d234576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233083, d234576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233084 q = 0) : d234577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233084, d234577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233166 q = 0) : d234621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233166, d234621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233166, d234621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
  have h15 (q : Pattern) (selected : d232989 q = 0) : d234485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
    | true =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233167 q = 0) : d234622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233167, d234622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233167, d234622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232990 q = 0) : d234486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d233168 q = 0) : d234623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233168, d234623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233168, d234623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d233169 q = 0) : d234624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233169, d234624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d233169, d234624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d233170 q = 0) : d234625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233170, d234625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d233170, d234625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d233171 q = 0) : d234626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233171, d234626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233171, d234626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23349 (p : Pattern) (selected : d233172 p = 0) : d234627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233166 q = 0) : d234621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233166, d234621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233166, d234621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
  have h2 (q : Pattern) (selected : d232989 q = 0) : d234485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23313 q selected
    | true =>
      simp only [d232989, d234485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233167 q = 0) : d234622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233167, d234622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233167, d234622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232990 q = 0) : d234486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232990, d234486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233168 q = 0) : d234623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233168, d234623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233168, d234623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233169 q = 0) : d234624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233169, d234624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233169, d234624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233170 q = 0) : d234625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233170, d234625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233170, d234625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233172 q = 0) : d234627 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233172, d234627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233172, d234627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23350 (p : Pattern) (selected : d233178 p = 0) : d234633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233091 q = 0) : d234584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23333 q selected
    | true =>
      simp only [d233091, d234584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
  have h2 (q : Pattern) (selected : d233092 q = 0) : d234585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233092, d234585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233093 q = 0) : d234586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233093, d234586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233096 q = 0) : d234589 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23334 q selected
    | true =>
      simp only [d233096, d234589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23335 q selected
  have h5 (q : Pattern) (selected : d233097 q = 0) : d234590 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233097, d234590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233098 q = 0) : d234591 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233098, d234591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233099 q = 0) : d234592 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233099, d234592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233173 q = 0) : d234628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233173, d234628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23348 q selected
    | true =>
      simp only [d233173, d234628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23349 q selected
  have h9 (q : Pattern) (selected : d233174 q = 0) : d234629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233174, d234629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233174, d234629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233175 q = 0) : d234630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233175, d234630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233175, d234630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233176 q = 0) : d234631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233176, d234631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233176, d234631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d233177 q = 0) : d234632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233177, d234632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233177, d234632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233178 q = 0) : d234633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233178, d234633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233178, d234633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23351 (p : Pattern) (selected : d233184 p = 0) : d234639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233179 q = 0) : d234634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233179, d234634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23350 q selected
    | true =>
      simp only [d233179, d234634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233180 q = 0) : d234635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233180, d234635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233180, d234635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233181 q = 0) : d234636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233181, d234636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233181, d234636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233182 q = 0) : d234637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233182, d234637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233182, d234637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233183 q = 0) : d234638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233183, d234638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233183, d234638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233184 q = 0) : d234639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233184, d234639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233184, d234639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23352 (p : Pattern) (selected : d233190 p = 0) : d234645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233121 q = 0) : d234614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233121, d234614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23338 q selected
    | true =>
      simp only [d233121, d234614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23340 q selected
  have h2 (q : Pattern) (selected : d233164 q = 0) : d234619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233164, d234619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23346 q selected
    | true =>
      simp only [d233164, d234619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23347 q selected
  have h3 (q : Pattern) (selected : d233165 q = 0) : d234620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233165, d234620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233165, d234620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233185 q = 0) : d234640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233185, d234640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23351 q selected
    | true =>
      simp only [d233185, d234640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233186 q = 0) : d234641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233186, d234641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233186, d234641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233187 q = 0) : d234642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233187, d234642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233187, d234642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233188 q = 0) : d234643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233188, d234643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233188, d234643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233189 q = 0) : d234644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233189, d234644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233189, d234644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d233190 q = 0) : d234645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233190, d234645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233190, d234645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23353 (p : Pattern) (selected : d233195 p = 0) : d234618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233115 q = 0) : d234608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233115, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23339 q selected
    | true =>
      simp only [d233115, d234608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233116 q = 0) : d234609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233116, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233116, d234609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233192 q = 0) : d234615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233192, d234615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233192, d234615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233193 q = 0) : d234616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233193, d234616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233193, d234616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233194 q = 0) : d234617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233194, d234617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233194, d234617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233195 q = 0) : d234618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233195, d234618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233195, d234618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23354 (p : Pattern) (selected : d233201 p = 0) : d234652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233196 q = 0) : d234647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233196, d234647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23353 q selected
    | true =>
      simp only [d233196, d234647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233197 q = 0) : d234648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233197, d234648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233197, d234648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233198 q = 0) : d234649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233198, d234649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233198, d234649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233199 q = 0) : d234650 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233199, d234650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233199, d234650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233200 q = 0) : d234651 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233200, d234651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233200, d234651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233201 q = 0) : d234652 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233201, d234652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233201, d234652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23355 (p : Pattern) (selected : d233207 p = 0) : d234658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232887 q = 0) : d234433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232887, d234433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232887, d234433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23291 q selected
  have h2 (q : Pattern) (selected : d232888 q = 0) : d234434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232888, d234434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232888, d234434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232897 q = 0) : d234443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232897, d234443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23291 q selected
    | true =>
      simp only [d232897, d234443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23294 q selected
  have h4 (q : Pattern) (selected : d232898 q = 0) : d234444 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232898, d234444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232898, d234444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232899 q = 0) : d234445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232899, d234445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232899, d234445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233038 q = 0) : d234531 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233038, d234531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23318 q selected
    | true =>
      simp only [d233038, d234531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23327 q selected
  have h7 (q : Pattern) (selected : d233051 q = 0) : d234544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233051, d234544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23328 q selected
    | true =>
      simp only [d233051, d234544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23329 q selected
  have h8 (q : Pattern) (selected : d233052 q = 0) : d234545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233052, d234545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233052, d234545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d233053 q = 0) : d234546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233053, d234546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d233053, d234546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d233054 q = 0) : d234547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233054, d234547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233054, d234547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233058 q = 0) : d234551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233058, d234551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233058, d234551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23330 q selected
  have h12 (q : Pattern) (selected : d233060 q = 0) : d234553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233060, d234553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233060, d234553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23331 q selected
  have h13 (q : Pattern) (selected : d233061 q = 0) : d234554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233061, d234554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233061, d234554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233062 q = 0) : d234555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233062, d234555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233062, d234555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d233063 q = 0) : d234556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233063, d234556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233063, d234556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233064 q = 0) : d234557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233064, d234557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233064, d234557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d233191 q = 0) : d234646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233191, d234646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233191, d234646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23352 q selected
  have h18 (q : Pattern) (selected : d233202 q = 0) : d234653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233202, d234653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233202, d234653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23354 q selected
  have h19 (q : Pattern) (selected : d233203 q = 0) : d234654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233203, d234654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d233203, d234654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d233204 q = 0) : d234655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233204, d234655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d233204, d234655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d233205 q = 0) : d234656 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233205, d234656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d233205, d234656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d233206 q = 0) : d234657 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233206, d234657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d233206, d234657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d233207 q = 0) : d234658 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d233207, d234658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233207, d234658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro23356 (p : Pattern) (selected : d233213 p = 0) : d234664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233208 q = 0) : d234659 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d233208, d234659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233208, d234659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23355 q selected
  have h2 (q : Pattern) (selected : d233209 q = 0) : d234660 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d233209, d234660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233209, d234660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233210 q = 0) : d234661 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d233210, d234661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233210, d234661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233211 q = 0) : d234662 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d233211, d234662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233211, d234662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233212 q = 0) : d234663 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d233212, d234663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233212, d234663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233213 q = 0) : d234664 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d233213, d234664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233213, d234664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23357 (p : Pattern) (selected : d233219 p = 0) : d234670 p = 1 := by
  have h0 (q : Pattern) (selected : d231806 q = 0) : d233601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231806, d233601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23041 q selected
    | true =>
      simp only [d231806, d233601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23075 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d232067 q = 0) : d233802 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232067, d233802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232067, d233802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23129 q selected
  have h3 (q : Pattern) (selected : d232068 q = 0) : d233803 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232068, d233803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232068, d233803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232441 q = 0) : d234082 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232441, d234082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232441, d234082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23204 q selected
  have h5 (q : Pattern) (selected : d232442 q = 0) : d234083 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232442, d234083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232442, d234083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232443 q = 0) : d234084 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d232443, d234084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232443, d234084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232828 q = 0) : d234374 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232828, d234374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232828, d234374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23280 q selected
  have h8 (q : Pattern) (selected : d232829 q = 0) : d234375 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232829, d234375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232829, d234375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232830 q = 0) : d234376 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d232830, d234376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232830, d234376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232831 q = 0) : d234377 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d232831, d234377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232831, d234377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233214 q = 0) : d234665 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233214, d234665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233214, d234665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23356 q selected
  have h12 (q : Pattern) (selected : d233215 q = 0) : d234666 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d233215, d234666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233215, d234666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233216 q = 0) : d234667 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d233216, d234667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233216, d234667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233217 q = 0) : d234668 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d233217, d234668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233217, d234668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d233218 q = 0) : d234669 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d233218, d234669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233218, d234669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233219 q = 0) : d234670 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d233219, d234670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d233219, d234670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro23358 (p : Pattern) (selected : d233225 p = 0) : d234676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233220 q = 0) : d234671 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d233220, d234671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23357 q selected
    | true =>
      simp only [d233220, d234671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233221 q = 0) : d234672 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d233221, d234672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233221, d234672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233222 q = 0) : d234673 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d233222, d234673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233222, d234673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233223 q = 0) : d234674 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d233223, d234674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233223, d234674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233224 q = 0) : d234675 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d233224, d234675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233224, d234675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233225 q = 0) : d234676 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d233225, d234676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233225, d234676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23359 (p : Pattern) (selected : d233231 p = 0) : d234682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233226 q = 0) : d234677 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d233226, d234677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23358 q selected
    | true =>
      simp only [d233226, d234677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233227 q = 0) : d234678 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d233227, d234678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233227, d234678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233228 q = 0) : d234679 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d233228, d234679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233228, d234679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233229 q = 0) : d234680 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d233229, d234680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233229, d234680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233230 q = 0) : d234681 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d233230, d234681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233230, d234681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233231 q = 0) : d234682 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d233231, d234682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233231, d234682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23360 (p : Pattern) (selected : d233237 p = 0) : d234688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233232 q = 0) : d234683 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d233232, d234683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23359 q selected
    | true =>
      simp only [d233232, d234683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233233 q = 0) : d234684 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d233233, d234684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233233, d234684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233234 q = 0) : d234685 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d233234, d234685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233234, d234685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233235 q = 0) : d234686 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d233235, d234686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233235, d234686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233236 q = 0) : d234687 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d233236, d234687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233236, d234687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233237 q = 0) : d234688 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d233237, d234688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233237, d234688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23361 (p : Pattern) (selected : d233243 p = 0) : d234694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233238 q = 0) : d234689 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d233238, d234689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23360 q selected
    | true =>
      simp only [d233238, d234689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233239 q = 0) : d234690 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d233239, d234690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233239, d234690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233240 q = 0) : d234691 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d233240, d234691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233240, d234691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233241 q = 0) : d234692 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d233241, d234692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233241, d234692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233242 q = 0) : d234693 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d233242, d234693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233242, d234693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233243 q = 0) : d234694 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d233243, d234694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233243, d234694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23362 (p : Pattern) (selected : d233249 p = 0) : d234700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233244 q = 0) : d234695 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d233244, d234695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23361 q selected
    | true =>
      simp only [d233244, d234695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233245 q = 0) : d234696 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d233245, d234696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233245, d234696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233246 q = 0) : d234697 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d233246, d234697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233246, d234697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233247 q = 0) : d234698 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d233247, d234698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233247, d234698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233248 q = 0) : d234699 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d233248, d234699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233248, d234699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233249 q = 0) : d234700 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d233249, d234700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233249, d234700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23363 (p : Pattern) (selected : d233255 p = 0) : d234706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233250 q = 0) : d234701 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d233250, d234701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23362 q selected
    | true =>
      simp only [d233250, d234701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233251 q = 0) : d234702 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d233251, d234702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233251, d234702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233252 q = 0) : d234703 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d233252, d234703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233252, d234703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233253 q = 0) : d234704 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d233253, d234704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233253, d234704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233254 q = 0) : d234705 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d233254, d234705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233254, d234705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233255 q = 0) : d234706 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d233255, d234706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233255, d234706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23364 (p : Pattern) (selected : d233261 p = 0) : d234712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d233256 q = 0) : d234707 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d233256, d234707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23363 q selected
    | true =>
      simp only [d233256, d234707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233257 q = 0) : d234708 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d233257, d234708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233257, d234708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233258 q = 0) : d234709 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d233258, d234709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233258, d234709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233259 q = 0) : d234710 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d233259, d234710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233259, d234710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233260 q = 0) : d234711 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d233260, d234711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233260, d234711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233261 q = 0) : d234712 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d233261, d234712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233261, d234712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23365 (p : Pattern) (selected : d231510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231509 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231510 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro23366 (p : Pattern) (selected : d231516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231516 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23367 (p : Pattern) (selected : d231522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23366 q selected
    | true =>
      simp only [d231517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231521 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231522 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23368 (p : Pattern) (selected : d231528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23367 q selected
    | true =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23369 (p : Pattern) (selected : d231534 p = 1) : d236292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231481 q = 1) : d231481 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231487 q = 1) : d231487 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231508 q = 1) : d231508 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d231529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23368 q selected
    | true =>
      simp only [d231529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231530 q = 1) : d236288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231530, d236288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231530, d236288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231404 q = 1) : d231404 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d231531 q = 1) : d236289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231531, d236289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231531, d236289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231532 q = 1) : d236290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231532, d236290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231532, d236290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231533 q = 1) : d236291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231533, d236291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231533, d236291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231534 q = 1) : d236292 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231534, d236292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231534, d236292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23370 (p : Pattern) (selected : d231546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23367 q selected
    | true =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23371 (p : Pattern) (selected : d231552 p = 1) : d236297 p = 1 := by
  have h0 (q : Pattern) (selected : d231481 q = 1) : d231481 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231487 q = 1) : d231487 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231508 q = 1) : d231508 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d231529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23368 q selected
    | true =>
      simp only [d231529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231530 q = 1) : d236288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231530, d236288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231530, d236288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231404 q = 1) : d231404 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d231531 q = 1) : d236289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231531, d236289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231531, d236289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231532 q = 1) : d236290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231532, d236290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231532, d236290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231533 q = 1) : d236291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231533, d236291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231533, d236291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231539 q = 1) : d231539 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d231543 q = 1) : d231543 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d231545 q = 1) : d231545 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d231547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23370 q selected
    | true =>
      simp only [d231547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d231548 q = 1) : d236293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231548, d236293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231548, d236293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231411 q = 1) : d231411 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d231549 q = 1) : d236294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231549, d236294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231549, d236294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231550 q = 1) : d236295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231550, d236295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231550, d236295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231551 q = 1) : d236296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231551, d236296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231551, d236296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231552 q = 1) : d236297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231552, d236297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231552, d236297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23372 (p : Pattern) (selected : d231561 p = 1) : d236304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231545 q = 1) : d231545 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23370 q selected
    | true =>
      simp only [d231547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231548 q = 1) : d236293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231548, d236293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231548, d236293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231411 q = 1) : d231411 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231549 q = 1) : d236294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231549, d236294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231549, d236294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231559 q = 1) : d236302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231559, d236302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231559, d236302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231560 q = 1) : d236303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231560, d236303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231560, d236303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231561 q = 1) : d236304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231561, d236304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231561, d236304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23373 (p : Pattern) (selected : d231591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231586 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
  have h2 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231587 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231588 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231589 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231590 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231591 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23374 (p : Pattern) (selected : d231597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231592 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23373 q selected
    | true =>
      simp only [d231592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231593 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231594 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231595 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231596 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231597 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23375 (p : Pattern) (selected : d231603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231598 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23374 q selected
    | true =>
      simp only [d231598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231599 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231600 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231601 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231602 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231603 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23376 (p : Pattern) (selected : d231609 p = 1) : d236314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231585 q = 1) : d231585 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23375 q selected
    | true =>
      simp only [d231604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231605 q = 1) : d236310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231605, d236310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231605, d236310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231445 q = 1) : d231445 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231606 q = 1) : d236311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231606, d236311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231606, d236311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231607 q = 1) : d236312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231607, d236312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231607, d236312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231608 q = 1) : d236313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231608, d236313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231608, d236313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231609 q = 1) : d236314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231609, d236314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231609, d236314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23377 (p : Pattern) (selected : d231615 p = 1) : d236320 p = 1 := by
  have h0 (q : Pattern) (selected : d231475 q = 1) : d231475 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231553 q = 1) : d236298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231553, d236298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23369 q selected
    | true =>
      simp only [d231553, d236298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23371 q selected
  have h2 (q : Pattern) (selected : d231555 q = 1) : d231555 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231556 q = 1) : d236299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231556, d236299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231556, d236299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231557 q = 1) : d236300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231557, d236300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231557, d236300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231558 q = 1) : d236301 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231558, d236301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231558, d236301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231562 q = 1) : d236305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231562, d236305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231562, d236305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23372 q selected
  have h8 (q : Pattern) (selected : d231563 q = 1) : d236306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231563, d236306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231563, d236306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d231564 q = 1) : d236307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231564, d236307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231564, d236307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d231565 q = 1) : d236308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231565, d236308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231565, d236308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d231566 q = 1) : d236309 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231566, d236309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231566, d236309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231610 q = 1) : d236315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231610, d236315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231610, d236315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23376 q selected
  have h13 (q : Pattern) (selected : d231611 q = 1) : d236316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231611, d236316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231611, d236316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d231612 q = 1) : d236317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231612, d236317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231612, d236317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d231613 q = 1) : d236318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231613, d236318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231613, d236318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d231614 q = 1) : d236319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231614, d236319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231614, d236319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d231615 q = 1) : d236320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231615, d236320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231615, d236320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro23378 (p : Pattern) (selected : d231621 p = 1) : d236326 p = 1 := by
  have h0 (q : Pattern) (selected : d231460 q = 1) : d231460 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231616 q = 1) : d236321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231616, d236321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231616, d236321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23377 q selected
  have h3 (q : Pattern) (selected : d231617 q = 1) : d236322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231617, d236322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231617, d236322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231618 q = 1) : d236323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231618, d236323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231618, d236323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231619 q = 1) : d236324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231619, d236324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231619, d236324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231620 q = 1) : d236325 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231620, d236325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231620, d236325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231621 q = 1) : d236326 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231621, d236326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231621, d236326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23379 (p : Pattern) (selected : d231671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231670 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231509 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231671 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23380 (p : Pattern) (selected : d231677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
    | true =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231675 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231676 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231677 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23381 (p : Pattern) (selected : d231683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23380 q selected
    | true =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23366 q selected
  have h2 (q : Pattern) (selected : d231679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23366 q selected
    | true =>
      simp only [d231517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231682 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231683 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23382 (p : Pattern) (selected : d231689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23381 q selected
    | true =>
      simp only [d231684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23367 q selected
    | true =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23383 (p : Pattern) (selected : d231701 p = 1) : d236331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231642 q = 1) : d231642 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231648 q = 1) : d231648 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231669 q = 1) : d231669 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d231690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23382 q selected
    | true =>
      simp only [d231690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23368 q selected
  have h5 (q : Pattern) (selected : d231691 q = 1) : d236327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231691, d236327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231691, d236327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231697 q = 1) : d231697 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d231698 q = 1) : d236328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231698, d236328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231698, d236328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231699 q = 1) : d236329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231699, d236329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231699, d236329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231700 q = 1) : d236330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231700, d236330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231700, d236330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231701 q = 1) : d236331 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231701, d236331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231701, d236331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23384 (p : Pattern) (selected : d231713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23381 q selected
    | true =>
      simp only [d231684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231685 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231523 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23367 q selected
    | true =>
      simp only [d231523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231524 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23385 (p : Pattern) (selected : d231722 p = 1) : d236336 p = 1 := by
  have h0 (q : Pattern) (selected : d231642 q = 1) : d231642 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231648 q = 1) : d231648 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231669 q = 1) : d231669 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23382 q selected
    | true =>
      simp only [d231690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23368 q selected
  have h4 (q : Pattern) (selected : d231691 q = 1) : d236327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231691, d236327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231691, d236327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231697 q = 1) : d231697 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d231698 q = 1) : d236328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231698, d236328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231698, d236328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231699 q = 1) : d236329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231699, d236329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231699, d236329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231700 q = 1) : d236330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231700, d236330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231700, d236330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231706 q = 1) : d231706 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d231710 q = 1) : d231710 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d231712 q = 1) : d231712 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d231714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23384 q selected
    | true =>
      simp only [d231714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23370 q selected
  have h13 (q : Pattern) (selected : d231715 q = 1) : d236332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231715, d236332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231715, d236332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231718 q = 1) : d231718 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d231719 q = 1) : d236333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231719, d236333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231719, d236333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231720 q = 1) : d236334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231720, d236334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231720, d236334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231721 q = 1) : d236335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231721, d236335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231721, d236335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231722 q = 1) : d236336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231722, d236336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231722, d236336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23386 (p : Pattern) (selected : d231731 p = 1) : d236343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231712 q = 1) : d231712 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23384 q selected
    | true =>
      simp only [d231714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23370 q selected
  have h3 (q : Pattern) (selected : d231715 q = 1) : d236332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231715, d236332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231715, d236332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231718 q = 1) : d231718 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231719 q = 1) : d236333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231719, d236333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231719, d236333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231729 q = 1) : d236341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231729, d236341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231729, d236341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231730 q = 1) : d236342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231730, d236342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231730, d236342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231731 q = 1) : d236343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231731, d236343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231731, d236343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23387 (p : Pattern) (selected : d231763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231758 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
  have h2 (q : Pattern) (selected : d231672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
    | true =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231759 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231760 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231586 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
  have h8 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231587 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231588 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231589 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231762 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231590 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231763 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23388 (p : Pattern) (selected : d231769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231764 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23387 q selected
    | true =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23373 q selected
  have h2 (q : Pattern) (selected : d231765 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231766 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231592 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23373 q selected
    | true =>
      simp only [d231592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231593 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231594 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231767 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231595 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231768 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231769 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23389 (p : Pattern) (selected : d231775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231770 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23388 q selected
    | true =>
      simp only [d231770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231771 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231598 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23374 q selected
    | true =>
      simp only [d231598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231599 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231772 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231773 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23390 (p : Pattern) (selected : d231787 p = 1) : d236353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231757 q = 1) : d231757 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23389 q selected
    | true =>
      simp only [d231776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23375 q selected
  have h3 (q : Pattern) (selected : d231777 q = 1) : d236349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231777, d236349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231777, d236349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231783 q = 1) : d231783 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231784 q = 1) : d236350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231784, d236350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231784, d236350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231785 q = 1) : d236351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231785, d236351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231785, d236351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231786 q = 1) : d236352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231786, d236352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231786, d236352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231787 q = 1) : d236353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231787, d236353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231787, d236353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23391 (p : Pattern) (selected : d231799 p = 1) : d236359 p = 1 := by
  have h0 (q : Pattern) (selected : d231636 q = 1) : d231636 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231723 q = 1) : d236337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231723, d236337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23383 q selected
    | true =>
      simp only [d231723, d236337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23385 q selected
  have h2 (q : Pattern) (selected : d231725 q = 1) : d231725 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231726 q = 1) : d236338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231726, d236338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231726, d236338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231727 q = 1) : d236339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231727, d236339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231727, d236339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231728 q = 1) : d236340 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231728, d236340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231728, d236340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231732 q = 1) : d236344 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231732, d236344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231732, d236344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23386 q selected
  have h8 (q : Pattern) (selected : d231734 q = 1) : d231734 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d231735 q = 1) : d236345 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231735, d236345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231735, d236345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231736 q = 1) : d236346 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231736, d236346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231736, d236346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d231737 q = 1) : d236347 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231737, d236347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231737, d236347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d231738 q = 1) : d236348 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231738, d236348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231738, d236348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231788 q = 1) : d236354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231788, d236354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231788, d236354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23390 q selected
  have h14 (q : Pattern) (selected : d231794 q = 1) : d231794 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d231795 q = 1) : d236355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231795, d236355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231795, d236355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231796 q = 1) : d236356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231796, d236356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231796, d236356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d231797 q = 1) : d236357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231797, d236357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231797, d236357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d231798 q = 1) : d236358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231798, d236358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231798, d236358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d231799 q = 1) : d236359 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231799, d236359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231799, d236359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23392 (p : Pattern) (selected : d231805 p = 1) : d236365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231800 q = 1) : d236360 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231800, d236360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231800, d236360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23391 q selected
  have h2 (q : Pattern) (selected : d231801 q = 1) : d236361 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231801, d236361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231801, d236361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231802 q = 1) : d236362 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231802, d236362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231802, d236362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231803 q = 1) : d236363 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231803, d236363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231803, d236363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231804 q = 1) : d236364 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231804, d236364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231804, d236364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231805 q = 1) : d236365 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231805, d236365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231805, d236365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23393 (p : Pattern) (selected : d231882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d568 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231881 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231670 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231882 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23394 (p : Pattern) (selected : d231888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231883 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23393 q selected
    | true =>
      simp only [d231883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231884 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231885 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231886 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
    | true =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231674 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231675 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231887 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231676 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231888 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23395 (p : Pattern) (selected : d231895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231889 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23394 q selected
    | true =>
      simp only [d231889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23380 q selected
  have h2 (q : Pattern) (selected : d231890 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231891 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23380 q selected
    | true =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23366 q selected
  have h5 (q : Pattern) (selected : d231679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231892 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231894 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231895 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23396 (p : Pattern) (selected : d231899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23380 q selected
    | true =>
      simp only [d231678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23366 q selected
  have h2 (q : Pattern) (selected : d231679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231898 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231899 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23397 (p : Pattern) (selected : d231905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23395 q selected
    | true =>
      simp only [d231896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23396 q selected
    | true =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23398 (p : Pattern) (selected : d231909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23396 q selected
    | true =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23399 (p : Pattern) (selected : d231921 p = 1) : d236371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231850 q = 1) : d231850 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231859 q = 1) : d231859 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231880 q = 1) : d231880 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d231910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23397 q selected
    | true =>
      simp only [d231910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23398 q selected
  have h5 (q : Pattern) (selected : d231911 q = 1) : d236367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231911, d236367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231911, d236367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231917 q = 1) : d231917 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d231918 q = 1) : d236368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231918, d236368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231918, d236368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231919 q = 1) : d236369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231919, d236369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231919, d236369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231920 q = 1) : d236370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231920, d236370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231920, d236370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231921 q = 1) : d236371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231921, d236371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231921, d236371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23400 (p : Pattern) (selected : d231935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23395 q selected
    | true =>
      simp only [d231896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23396 q selected
    | true =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23401 (p : Pattern) (selected : d231936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23396 q selected
    | true =>
      simp only [d231900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231906 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231907 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23402 (p : Pattern) (selected : d231945 p = 1) : d236376 p = 1 := by
  have h0 (q : Pattern) (selected : d231850 q = 1) : d231850 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231859 q = 1) : d231859 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231880 q = 1) : d231880 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23397 q selected
    | true =>
      simp only [d231910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23398 q selected
  have h4 (q : Pattern) (selected : d231911 q = 1) : d236367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231911, d236367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231911, d236367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231917 q = 1) : d231917 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d231918 q = 1) : d236368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231918, d236368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231918, d236368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231919 q = 1) : d236369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231919, d236369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231919, d236369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231920 q = 1) : d236370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231920, d236370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231920, d236370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231927 q = 1) : d231927 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d231932 q = 1) : d231932 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d231934 q = 1) : d231934 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d231937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23400 q selected
    | true =>
      simp only [d231937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23401 q selected
  have h13 (q : Pattern) (selected : d231938 q = 1) : d236372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231938, d236372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231938, d236372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231941 q = 1) : d231941 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d231942 q = 1) : d236373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231942, d236373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231942, d236373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231943 q = 1) : d236374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231943, d236374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231943, d236374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231944 q = 1) : d236375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231944, d236375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231944, d236375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231945 q = 1) : d236376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231945, d236376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231945, d236376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23403 (p : Pattern) (selected : d231965 p = 1) : d236383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231934 q = 1) : d231934 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d231937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23400 q selected
    | true =>
      simp only [d231937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23401 q selected
  have h3 (q : Pattern) (selected : d231938 q = 1) : d236372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231938, d236372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231938, d236372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231941 q = 1) : d231941 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231942 q = 1) : d236373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231942, d236373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231942, d236373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231963 q = 1) : d236381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231963, d236381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231963, d236381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231964 q = 1) : d236382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231964, d236382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231964, d236382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231965 q = 1) : d236383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231965, d236383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231965, d236383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23404 (p : Pattern) (selected : d232010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232005 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23393 q selected
  have h2 (q : Pattern) (selected : d231883 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23393 q selected
    | true =>
      simp only [d231883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232006 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231884 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231758 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
  have h8 (q : Pattern) (selected : d231672 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23379 q selected
    | true =>
      simp only [d231672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231759 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231760 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231586 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
  have h15 (q : Pattern) (selected : d231511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23365 q selected
    | true =>
      simp only [d231511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231587 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231588 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231589 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d231762 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23405 (p : Pattern) (selected : d232017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23404 q selected
    | true =>
      simp only [d232011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23387 q selected
  have h2 (q : Pattern) (selected : d232012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231764 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23387 q selected
    | true =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23373 q selected
  have h5 (q : Pattern) (selected : d231765 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231766 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232016 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232017 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23406 (p : Pattern) (selected : d232021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231764 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23387 q selected
    | true =>
      simp only [d231764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23373 q selected
  have h2 (q : Pattern) (selected : d231765 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231766 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23407 (p : Pattern) (selected : d232027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232018 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23405 q selected
    | true =>
      simp only [d232018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232019 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23406 q selected
    | true =>
      simp only [d232022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23408 (p : Pattern) (selected : d232031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23406 q selected
    | true =>
      simp only [d232022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23409 (p : Pattern) (selected : d232043 p = 1) : d236393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232004 q = 1) : d232004 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23407 q selected
    | true =>
      simp only [d232032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23408 q selected
  have h3 (q : Pattern) (selected : d232033 q = 1) : d236389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232033, d236389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232033, d236389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232039 q = 1) : d232039 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232040 q = 1) : d236390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232040, d236390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232040, d236390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232041 q = 1) : d236391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232041, d236391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232041, d236391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232042 q = 1) : d236392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232042, d236392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232042, d236392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232043 q = 1) : d236393 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232043, d236393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232043, d236393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23410 (p : Pattern) (selected : d232060 p = 1) : d236399 p = 1 := by
  have h0 (q : Pattern) (selected : d231842 q = 1) : d231842 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d231946 q = 1) : d236377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231946, d236377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23399 q selected
    | true =>
      simp only [d231946, d236377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23402 q selected
  have h2 (q : Pattern) (selected : d231959 q = 1) : d231959 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d231960 q = 1) : d236378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231960, d236378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231960, d236378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d231961 q = 1) : d236379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231961, d236379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231961, d236379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231962 q = 1) : d236380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231962, d236380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231962, d236380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231966 q = 1) : d236384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231966, d236384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231966, d236384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23403 q selected
  have h8 (q : Pattern) (selected : d231968 q = 1) : d231968 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d231969 q = 1) : d236385 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231969, d236385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231969, d236385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231970 q = 1) : d236386 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231970, d236386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231970, d236386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d231971 q = 1) : d236387 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231971, d236387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231971, d236387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d231972 q = 1) : d236388 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231972, d236388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231972, d236388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232044 q = 1) : d236394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232044, d236394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232044, d236394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23409 q selected
  have h14 (q : Pattern) (selected : d232055 q = 1) : d232055 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d232056 q = 1) : d236395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232056, d236395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232056, d236395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232057 q = 1) : d236396 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232057, d236396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232057, d236396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d232058 q = 1) : d236397 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232058, d236397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232058, d236397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d232059 q = 1) : d236398 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232059, d236398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232059, d236398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d232060 q = 1) : d236399 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232060, d236399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232060, d236399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23411 (p : Pattern) (selected : d232066 p = 1) : d236405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232061 q = 1) : d236400 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232061, d236400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232061, d236400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23410 q selected
  have h2 (q : Pattern) (selected : d232062 q = 1) : d236401 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232062, d236401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232062, d236401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232063 q = 1) : d236402 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232063, d236402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232063, d236402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232064 q = 1) : d236403 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232064, d236403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232064, d236403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232065 q = 1) : d236404 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232065, d236404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232065, d236404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232066 q = 1) : d236405 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232066, d236405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232066, d236405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23412 (p : Pattern) (selected : d232176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro49 q selected
    | true =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232174 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h5 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232175 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232176 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23413 (p : Pattern) (selected : d232182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232175 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1259 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h5 (q : Pattern) (selected : d1260 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232181 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232182 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23414 (p : Pattern) (selected : d232188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1259 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1260 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232181 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d231509 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232188 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23415 (p : Pattern) (selected : d232194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23412 q selected
    | true =>
      simp only [d232177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
    | true =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232191 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232192 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232193 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232194 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23416 (p : Pattern) (selected : d232196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
    | true =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232191 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232192 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232193 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232195 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232196 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23417 (p : Pattern) (selected : d232200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232191 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232192 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232195 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232200 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23418 (p : Pattern) (selected : d232207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232197 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23415 q selected
    | true =>
      simp only [d232197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23416 q selected
  have h2 (q : Pattern) (selected : d232198 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232199 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232201 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23416 q selected
    | true =>
      simp only [d232201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23417 q selected
  have h5 (q : Pattern) (selected : d232202 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232203 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232204 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232205 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232206 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232207 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23419 (p : Pattern) (selected : d232211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232201 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23416 q selected
    | true =>
      simp only [d232201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23417 q selected
  have h2 (q : Pattern) (selected : d232202 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232203 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232205 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232210 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232211 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23420 (p : Pattern) (selected : d232217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23418 q selected
    | true =>
      simp only [d232208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23419 q selected
    | true =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232214 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232215 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232216 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232217 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23421 (p : Pattern) (selected : d232221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23419 q selected
    | true =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232218 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232219 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232221 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23422 (p : Pattern) (selected : d232244 p = 1) : d236412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232143 q = 1) : d232143 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232152 q = 1) : d232152 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232173 q = 1) : d232173 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d232222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23420 q selected
    | true =>
      simp only [d232222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23421 q selected
  have h5 (q : Pattern) (selected : d232223 q = 1) : d236408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232223, d236408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232223, d236408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232240 q = 1) : d232240 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d232241 q = 1) : d236409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232241, d236409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232241, d236409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232242 q = 1) : d236410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232242, d236410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232242, d236410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232243 q = 1) : d236411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232243, d236411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232243, d236411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232244 q = 1) : d236412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232244, d236412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232244, d236412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23423 (p : Pattern) (selected : d232258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23418 q selected
    | true =>
      simp only [d232208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23419 q selected
    | true =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232214 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232215 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232216 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232258 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23424 (p : Pattern) (selected : d232259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23419 q selected
    | true =>
      simp only [d232212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232218 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232219 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23425 (p : Pattern) (selected : d232268 p = 1) : d236417 p = 1 := by
  have h0 (q : Pattern) (selected : d232143 q = 1) : d232143 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232152 q = 1) : d232152 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232173 q = 1) : d232173 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23420 q selected
    | true =>
      simp only [d232222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23421 q selected
  have h4 (q : Pattern) (selected : d232223 q = 1) : d236408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232223, d236408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232223, d236408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232240 q = 1) : d232240 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d232241 q = 1) : d236409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232241, d236409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232241, d236409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232242 q = 1) : d236410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232242, d236410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232242, d236410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232243 q = 1) : d236411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232243, d236411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232243, d236411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232250 q = 1) : d232250 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d232255 q = 1) : d232255 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d232257 q = 1) : d232257 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d232260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23423 q selected
    | true =>
      simp only [d232260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23424 q selected
  have h13 (q : Pattern) (selected : d232261 q = 1) : d236413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232261, d236413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232261, d236413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232264 q = 1) : d232264 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d232265 q = 1) : d236414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232265, d236414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232265, d236414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232266 q = 1) : d236415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232266, d236415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232266, d236415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232267 q = 1) : d236416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232267, d236416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232267, d236416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d232268 q = 1) : d236417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232268, d236417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232268, d236417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23426 (p : Pattern) (selected : d232288 p = 1) : d236424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232257 q = 1) : d232257 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23423 q selected
    | true =>
      simp only [d232260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23424 q selected
  have h3 (q : Pattern) (selected : d232261 q = 1) : d236413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232261, d236413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232261, d236413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232264 q = 1) : d232264 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232265 q = 1) : d236414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232265, d236414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232265, d236414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232286 q = 1) : d236422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232286, d236422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232286, d236422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232287 q = 1) : d236423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232287, d236423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232287, d236423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232288 q = 1) : d236424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232288, d236424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232288, d236424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23427 (p : Pattern) (selected : d232367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232353 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23412 q selected
  have h2 (q : Pattern) (selected : d232177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23412 q selected
    | true =>
      simp only [d232177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232354 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232355 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232356 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
  have h8 (q : Pattern) (selected : d232183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
    | true =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232361 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232362 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
  have h15 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232363 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232364 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232365 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23428 (p : Pattern) (selected : d232369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232357 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
  have h2 (q : Pattern) (selected : d232183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23413 q selected
    | true =>
      simp only [d232183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232358 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232359 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232360 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232362 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
  have h8 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232363 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232364 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232365 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232369 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23429 (p : Pattern) (selected : d232373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232362 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
  have h2 (q : Pattern) (selected : d232189 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23414 q selected
    | true =>
      simp only [d232189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232363 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232190 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232364 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232365 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232373 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23430 (p : Pattern) (selected : d232380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23427 q selected
    | true =>
      simp only [d232370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23428 q selected
  have h2 (q : Pattern) (selected : d232371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23428 q selected
    | true =>
      simp only [d232374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23429 q selected
  have h5 (q : Pattern) (selected : d232375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232379 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232380 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23431 (p : Pattern) (selected : d232384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232374 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23428 q selected
    | true =>
      simp only [d232374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23429 q selected
  have h2 (q : Pattern) (selected : d232375 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232376 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232383 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232384 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23432 (p : Pattern) (selected : d232390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23430 q selected
    | true =>
      simp only [d232381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232382 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232385 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23431 q selected
    | true =>
      simp only [d232385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232386 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232387 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232388 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23433 (p : Pattern) (selected : d232394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232385 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23431 q selected
    | true =>
      simp only [d232385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232386 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232391 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232392 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232393 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23434 (p : Pattern) (selected : d232417 p = 1) : d236434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232352 q = 1) : d232352 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232395 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23432 q selected
    | true =>
      simp only [d232395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23433 q selected
  have h3 (q : Pattern) (selected : d232396 q = 1) : d236430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232396, d236430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232396, d236430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232413 q = 1) : d232413 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232414 q = 1) : d236431 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232414, d236431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232414, d236431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232415 q = 1) : d236432 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232415, d236432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232415, d236432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232416 q = 1) : d236433 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232416, d236433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232416, d236433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232417 q = 1) : d236434 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232417, d236434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232417, d236434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23435 (p : Pattern) (selected : d232434 p = 1) : d236440 p = 1 := by
  have h0 (q : Pattern) (selected : d232135 q = 1) : d232135 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232269 q = 1) : d236418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232269, d236418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23422 q selected
    | true =>
      simp only [d232269, d236418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23425 q selected
  have h2 (q : Pattern) (selected : d232282 q = 1) : d232282 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232283 q = 1) : d236419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232283, d236419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232283, d236419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232284 q = 1) : d236420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232284, d236420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232284, d236420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232285 q = 1) : d236421 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232285, d236421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232285, d236421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232289 q = 1) : d236425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232289, d236425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232289, d236425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23426 q selected
  have h8 (q : Pattern) (selected : d232291 q = 1) : d232291 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d232292 q = 1) : d236426 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232292, d236426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232292, d236426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232293 q = 1) : d236427 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232293, d236427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232293, d236427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d232294 q = 1) : d236428 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232294, d236428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232294, d236428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d232295 q = 1) : d236429 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232295, d236429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232295, d236429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232418 q = 1) : d236435 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232418, d236435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232418, d236435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23434 q selected
  have h14 (q : Pattern) (selected : d232429 q = 1) : d232429 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d232430 q = 1) : d236436 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232430, d236436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232430, d236436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232431 q = 1) : d236437 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232431, d236437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232431, d236437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d232432 q = 1) : d236438 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232432, d236438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232432, d236438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d232433 q = 1) : d236439 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232433, d236439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232433, d236439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d232434 q = 1) : d236440 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232434, d236440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232434, d236440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23436 (p : Pattern) (selected : d232440 p = 1) : d236446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232435 q = 1) : d236441 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232435, d236441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232435, d236441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23435 q selected
  have h2 (q : Pattern) (selected : d232436 q = 1) : d236442 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232436, d236442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232436, d236442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232437 q = 1) : d236443 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232437, d236443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232437, d236443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232438 q = 1) : d236444 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232438, d236444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232438, d236444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232439 q = 1) : d236445 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232439, d236445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232439, d236445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232440 q = 1) : d236446 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232440, d236446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232440, d236446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23437 (p : Pattern) (selected : d232552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro106 q selected
    | true =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro107 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h3 (q : Pattern) (selected : d1697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232550 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h6 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h7 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232551 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232552 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23438 (p : Pattern) (selected : d232558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232551 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h6 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h7 (q : Pattern) (selected : d1732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232557 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232558 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23439 (p : Pattern) (selected : d232565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h3 (q : Pattern) (selected : d1732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232557 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232564 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232565 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23440 (p : Pattern) (selected : d232571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23437 q selected
    | true =>
      simp only [d232553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232555 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232556 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232559 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
    | true =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232561 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232562 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232563 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232568 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232569 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232571 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23441 (p : Pattern) (selected : d232573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232559 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
    | true =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232561 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232562 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232568 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232569 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232573 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23442 (p : Pattern) (selected : d232577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232568 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232569 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232577 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23443 (p : Pattern) (selected : d232584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23440 q selected
    | true =>
      simp only [d232574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23441 q selected
  have h2 (q : Pattern) (selected : d232575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232578 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23441 q selected
    | true =>
      simp only [d232578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23442 q selected
  have h5 (q : Pattern) (selected : d232579 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232581 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232583 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232584 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23444 (p : Pattern) (selected : d232588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232578 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23441 q selected
    | true =>
      simp only [d232578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23442 q selected
  have h2 (q : Pattern) (selected : d232579 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232587 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232588 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23445 (p : Pattern) (selected : d232594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23443 q selected
    | true =>
      simp only [d232585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23444 q selected
    | true =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23446 (p : Pattern) (selected : d232598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23444 q selected
    | true =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23447 (p : Pattern) (selected : d232627 p = 1) : d236454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232519 q = 1) : d232519 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232528 q = 1) : d232528 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232549 q = 1) : d232549 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d232599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23445 q selected
    | true =>
      simp only [d232599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23446 q selected
  have h5 (q : Pattern) (selected : d232600 q = 1) : d236450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232600, d236450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232600, d236450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232623 q = 1) : d232623 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d232624 q = 1) : d236451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232624, d236451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232624, d236451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232625 q = 1) : d236452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232625, d236452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232625, d236452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232626 q = 1) : d236453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232626, d236453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232626, d236453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232627 q = 1) : d236454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232627, d236454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232627, d236454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23448 (p : Pattern) (selected : d232641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23443 q selected
    | true =>
      simp only [d232585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23444 q selected
    | true =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23449 (p : Pattern) (selected : d232642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232589 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23444 q selected
    | true =>
      simp only [d232589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232590 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23450 (p : Pattern) (selected : d232651 p = 1) : d236459 p = 1 := by
  have h0 (q : Pattern) (selected : d232519 q = 1) : d232519 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232528 q = 1) : d232528 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232549 q = 1) : d232549 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23445 q selected
    | true =>
      simp only [d232599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23446 q selected
  have h4 (q : Pattern) (selected : d232600 q = 1) : d236450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232600, d236450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232600, d236450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232623 q = 1) : d232623 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d232624 q = 1) : d236451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232624, d236451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232624, d236451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232625 q = 1) : d236452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232625, d236452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232625, d236452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232626 q = 1) : d236453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232626, d236453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232626, d236453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232633 q = 1) : d232633 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d232638 q = 1) : d232638 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d232640 q = 1) : d232640 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d232643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23448 q selected
    | true =>
      simp only [d232643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23449 q selected
  have h13 (q : Pattern) (selected : d232644 q = 1) : d236455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232644, d236455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232644, d236455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232647 q = 1) : d232647 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d232648 q = 1) : d236456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232648, d236456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232648, d236456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232649 q = 1) : d236457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232649, d236457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232649, d236457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232650 q = 1) : d236458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232650, d236458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232650, d236458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d232651 q = 1) : d236459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232651, d236459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232651, d236459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23451 (p : Pattern) (selected : d232671 p = 1) : d236466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232640 q = 1) : d232640 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23448 q selected
    | true =>
      simp only [d232643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23449 q selected
  have h3 (q : Pattern) (selected : d232644 q = 1) : d236455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232644, d236455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232644, d236455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232647 q = 1) : d232647 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232648 q = 1) : d236456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232648, d236456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232648, d236456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232669 q = 1) : d236464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232669, d236464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232669, d236464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232670 q = 1) : d236465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232670, d236465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232670, d236465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232671 q = 1) : d236466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232671, d236466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232671, d236466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23452 (p : Pattern) (selected : d232750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23437 q selected
  have h2 (q : Pattern) (selected : d232553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23437 q selected
    | true =>
      simp only [d232553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232740 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
  have h8 (q : Pattern) (selected : d232559 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
    | true =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232741 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232742 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232743 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232744 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
  have h15 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232750 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23453 (p : Pattern) (selected : d232752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232740 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
  have h2 (q : Pattern) (selected : d232559 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23438 q selected
    | true =>
      simp only [d232559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232741 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232742 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232743 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
  have h8 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232749 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232751 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232752 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23454 (p : Pattern) (selected : d232756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
  have h2 (q : Pattern) (selected : d232566 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23439 q selected
    | true =>
      simp only [d232566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232747 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232748 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232751 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232756 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23455 (p : Pattern) (selected : d232763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232753 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23452 q selected
    | true =>
      simp only [d232753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23453 q selected
  have h2 (q : Pattern) (selected : d232754 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232755 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23453 q selected
    | true =>
      simp only [d232757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23454 q selected
  have h5 (q : Pattern) (selected : d232758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232761 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232762 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232763 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23456 (p : Pattern) (selected : d232767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23453 q selected
    | true =>
      simp only [d232757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23454 q selected
  have h2 (q : Pattern) (selected : d232758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232761 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232767 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23457 (p : Pattern) (selected : d232773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232764 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23455 q selected
    | true =>
      simp only [d232764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232765 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23456 q selected
    | true =>
      simp only [d232768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232770 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232771 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232772 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23458 (p : Pattern) (selected : d232777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23456 q selected
    | true =>
      simp only [d232768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23459 (p : Pattern) (selected : d232804 p = 1) : d236476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232735 q = 1) : d232735 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23457 q selected
    | true =>
      simp only [d232778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23458 q selected
  have h3 (q : Pattern) (selected : d232779 q = 1) : d236472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232779, d236472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232779, d236472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232800 q = 1) : d232800 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232801 q = 1) : d236473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232801, d236473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232801, d236473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232802 q = 1) : d236474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232802, d236474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232802, d236474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232803 q = 1) : d236475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232803, d236475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232803, d236475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232804 q = 1) : d236476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232804, d236476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232804, d236476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23460 (p : Pattern) (selected : d232821 p = 1) : d236482 p = 1 := by
  have h0 (q : Pattern) (selected : d232511 q = 1) : d232511 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232652 q = 1) : d236460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232652, d236460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23447 q selected
    | true =>
      simp only [d232652, d236460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23450 q selected
  have h2 (q : Pattern) (selected : d232665 q = 1) : d232665 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232666 q = 1) : d236461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232666, d236461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232666, d236461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d232667 q = 1) : d236462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232667, d236462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232667, d236462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232668 q = 1) : d236463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232668, d236463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232668, d236463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232672 q = 1) : d236467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232672, d236467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232672, d236467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23451 q selected
  have h8 (q : Pattern) (selected : d232674 q = 1) : d232674 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d232675 q = 1) : d236468 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232675, d236468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232675, d236468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232676 q = 1) : d236469 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232676, d236469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232676, d236469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d232677 q = 1) : d236470 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232677, d236470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232677, d236470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d232678 q = 1) : d236471 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232678, d236471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232678, d236471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232805 q = 1) : d236477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232805, d236477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232805, d236477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23459 q selected
  have h14 (q : Pattern) (selected : d232816 q = 1) : d232816 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d232817 q = 1) : d236478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232817, d236478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232817, d236478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232818 q = 1) : d236479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232818, d236479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232818, d236479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d232819 q = 1) : d236480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232819, d236480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232819, d236480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d232820 q = 1) : d236481 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232820, d236481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232820, d236481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d232821 q = 1) : d236482 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232821, d236482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232821, d236482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23461 (p : Pattern) (selected : d232827 p = 1) : d236488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232822 q = 1) : d236483 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232822, d236483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232822, d236483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23460 q selected
  have h2 (q : Pattern) (selected : d232823 q = 1) : d236484 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232823, d236484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232823, d236484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232824 q = 1) : d236485 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232824, d236485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232824, d236485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232825 q = 1) : d236486 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232825, d236486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232825, d236486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232826 q = 1) : d236487 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232826, d236487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232826, d236487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232827 q = 1) : d236488 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232827, d236488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232827, d236488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23462 (p : Pattern) (selected : d232939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro141 q selected
    | true =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro142 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h3 (q : Pattern) (selected : d2175 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232937 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h6 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h7 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232938 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232939 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23463 (p : Pattern) (selected : d232945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232938 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro149 q selected
    | true =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h6 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h7 (q : Pattern) (selected : d2210 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232944 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232945 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23464 (p : Pattern) (selected : d232952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro149 q selected
    | true =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d2210 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232944 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232951 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232952 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23465 (p : Pattern) (selected : d232958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232940 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23462 q selected
    | true =>
      simp only [d232940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232941 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232942 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232943 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
    | true =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232950 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232955 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232956 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232957 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232958 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23466 (p : Pattern) (selected : d232960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
    | true =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232955 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232956 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232957 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232960 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23467 (p : Pattern) (selected : d232964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232955 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232956 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232959 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232964 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23468 (p : Pattern) (selected : d232971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232961 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23465 q selected
    | true =>
      simp only [d232961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23466 q selected
  have h2 (q : Pattern) (selected : d232962 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232963 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23466 q selected
    | true =>
      simp only [d232965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23467 q selected
  have h5 (q : Pattern) (selected : d232966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232969 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232970 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232971 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23469 (p : Pattern) (selected : d232975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23466 q selected
    | true =>
      simp only [d232965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23467 q selected
  have h2 (q : Pattern) (selected : d232966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232969 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232974 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232975 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23470 (p : Pattern) (selected : d232981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232972 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23468 q selected
    | true =>
      simp only [d232972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232973 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232976 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23469 q selected
    | true =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232977 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232978 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232979 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232980 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232981 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23471 (p : Pattern) (selected : d232985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232976 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23469 q selected
    | true =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232977 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232982 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232983 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232984 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23472 (p : Pattern) (selected : d233013 p = 1) : d236497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232907 q = 1) : d232907 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232916 q = 1) : d232916 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232936 q = 1) : d232936 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d232986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23470 q selected
    | true =>
      simp only [d232986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23471 q selected
  have h5 (q : Pattern) (selected : d232987 q = 1) : d236493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232987, d236493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232987, d236493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233009 q = 1) : d233009 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d233010 q = 1) : d236494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233010, d236494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233010, d236494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233011 q = 1) : d236495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233011, d236495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233011, d236495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d233012 q = 1) : d236496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233012, d236496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233012, d236496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233013 q = 1) : d236497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233013, d236497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233013, d236497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro23473 (p : Pattern) (selected : d233027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232972 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23468 q selected
    | true =>
      simp only [d232972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232973 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232976 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23469 q selected
    | true =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232977 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232978 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232979 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232980 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23474 (p : Pattern) (selected : d233028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232976 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23469 q selected
    | true =>
      simp only [d232976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232977 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232982 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232983 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232984 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233028 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23475 (p : Pattern) (selected : d233037 p = 1) : d236502 p = 1 := by
  have h0 (q : Pattern) (selected : d232907 q = 1) : d232907 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d232916 q = 1) : d232916 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232936 q = 1) : d232936 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d232986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23470 q selected
    | true =>
      simp only [d232986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23471 q selected
  have h4 (q : Pattern) (selected : d232987 q = 1) : d236493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232987, d236493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232987, d236493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233009 q = 1) : d233009 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d233010 q = 1) : d236494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233010, d236494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233010, d236494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233011 q = 1) : d236495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233011, d236495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233011, d236495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233012 q = 1) : d236496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233012, d236496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233012, d236496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d233019 q = 1) : d233019 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d233024 q = 1) : d233024 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d233026 q = 1) : d233026 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d233029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23473 q selected
    | true =>
      simp only [d233029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23474 q selected
  have h13 (q : Pattern) (selected : d233030 q = 1) : d236498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233030, d236498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233030, d236498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233033 q = 1) : d233033 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d233034 q = 1) : d236499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233034, d236499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233034, d236499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233035 q = 1) : d236500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233035, d236500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233035, d236500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d233036 q = 1) : d236501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233036, d236501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233036, d236501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d233037 q = 1) : d236502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233037, d236502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d233037, d236502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23476 (p : Pattern) (selected : d233057 p = 1) : d236509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233026 q = 1) : d233026 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d233029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23473 q selected
    | true =>
      simp only [d233029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23474 q selected
  have h3 (q : Pattern) (selected : d233030 q = 1) : d236498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233030, d236498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233030, d236498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233033 q = 1) : d233033 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d233034 q = 1) : d236499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233034, d236499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233034, d236499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233055 q = 1) : d236507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233055, d236507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233055, d236507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233056 q = 1) : d236508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233056, d236508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233056, d236508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233057 q = 1) : d236509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233057, d236509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233057, d236509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23477 (p : Pattern) (selected : d233136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233122 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23462 q selected
  have h2 (q : Pattern) (selected : d232940 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23462 q selected
    | true =>
      simp only [d232940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233123 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232941 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233124 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233125 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
  have h8 (q : Pattern) (selected : d232946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
    | true =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233130 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
  have h15 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d233132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d233133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d233134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d233135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d233136 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23478 (p : Pattern) (selected : d233138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233126 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
  have h2 (q : Pattern) (selected : d232946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23463 q selected
    | true =>
      simp only [d232946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233127 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233128 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233129 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
  have h8 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d233133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d233134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d233135 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233137 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d233138 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23479 (p : Pattern) (selected : d233142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
  have h2 (q : Pattern) (selected : d232953 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23464 q selected
    | true =>
      simp only [d232953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233137 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d233137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233142 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d233142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23480 (p : Pattern) (selected : d233149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233139 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23477 q selected
    | true =>
      simp only [d233139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23478 q selected
  have h2 (q : Pattern) (selected : d233140 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233141 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233143 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23478 q selected
    | true =>
      simp only [d233143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23479 q selected
  have h5 (q : Pattern) (selected : d233144 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233145 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233146 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233147 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d233148 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233149 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23481 (p : Pattern) (selected : d233153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233143 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d233143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23478 q selected
    | true =>
      simp only [d233143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23479 q selected
  have h2 (q : Pattern) (selected : d233144 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233145 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d233145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233147 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d233147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233152 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d233152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233153 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d233153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23482 (p : Pattern) (selected : d233159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233150 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23480 q selected
    | true =>
      simp only [d233150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233151 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23481 q selected
    | true =>
      simp only [d233154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233156 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233157 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d233158 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d233159 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23483 (p : Pattern) (selected : d233163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d233154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23481 q selected
    | true =>
      simp only [d233154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d233155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233160 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d233160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d233161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d233162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d233163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23484 (p : Pattern) (selected : d233190 p = 1) : d236519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233121 q = 1) : d233121 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d233164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d233164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23482 q selected
    | true =>
      simp only [d233164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23483 q selected
  have h3 (q : Pattern) (selected : d233165 q = 1) : d236515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d233165, d236515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233165, d236515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233186 q = 1) : d233186 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d233187 q = 1) : d236516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d233187, d236516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233187, d236516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233188 q = 1) : d236517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d233188, d236517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233188, d236517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233189 q = 1) : d236518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d233189, d236518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233189, d236518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d233190 q = 1) : d236519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d233190, d236519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233190, d236519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23485 (p : Pattern) (selected : d233207 p = 1) : d236525 p = 1 := by
  have h0 (q : Pattern) (selected : d232899 q = 1) : d232899 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233038 q = 1) : d236503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233038, d236503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23472 q selected
    | true =>
      simp only [d233038, d236503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23475 q selected
  have h2 (q : Pattern) (selected : d233051 q = 1) : d233051 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d233052 q = 1) : d236504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233052, d236504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233052, d236504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d233053 q = 1) : d236505 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233053, d236505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233053, d236505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233054 q = 1) : d236506 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233054, d236506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233054, d236506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d233058 q = 1) : d236510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233058, d236510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233058, d236510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23476 q selected
  have h8 (q : Pattern) (selected : d233060 q = 1) : d233060 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d233061 q = 1) : d236511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233061, d236511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d233061, d236511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d233062 q = 1) : d236512 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233062, d236512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d233062, d236512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d233063 q = 1) : d236513 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233063, d236513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233063, d236513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d233064 q = 1) : d236514 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233064, d236514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d233064, d236514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233191 q = 1) : d236520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d233191, d236520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233191, d236520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23484 q selected
  have h14 (q : Pattern) (selected : d233202 q = 1) : d233202 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d233203 q = 1) : d236521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d233203, d236521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d233203, d236521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233204 q = 1) : d236522 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d233204, d236522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d233204, d236522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d233205 q = 1) : d236523 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d233205, d236523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d233205, d236523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d233206 q = 1) : d236524 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d233206, d236524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d233206, d236524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d233207 q = 1) : d236525 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d233207, d236525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d233207, d236525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23486 (p : Pattern) (selected : d233213 p = 1) : d236531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233208 q = 1) : d236526 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d233208, d236526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233208, d236526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23485 q selected
  have h2 (q : Pattern) (selected : d233209 q = 1) : d236527 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d233209, d236527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233209, d236527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d233210 q = 1) : d236528 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d233210, d236528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233210, d236528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d233211 q = 1) : d236529 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d233211, d236529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233211, d236529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d233212 q = 1) : d236530 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d233212, d236530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233212, d236530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d233213 q = 1) : d236531 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d233213, d236531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233213, d236531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23487 (p : Pattern) (selected : d233219 p = 1) : d236537 p = 1 := by
  have h0 (q : Pattern) (selected : d231806 q = 1) : d236366 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231806, d236366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23378 q selected
    | true =>
      simp only [d231806, d236366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23392 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d232067 q = 1) : d236406 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232067, d236406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232067, d236406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23411 q selected
  have h3 (q : Pattern) (selected : d232068 q = 1) : d236407 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232068, d236407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232068, d236407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232441 q = 1) : d236447 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232441, d236447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232441, d236447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23436 q selected
  have h5 (q : Pattern) (selected : d232442 q = 1) : d236448 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232442, d236448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232442, d236448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232443 q = 1) : d236449 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d232443, d236449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232443, d236449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232828 q = 1) : d236489 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d232828, d236489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232828, d236489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23461 q selected
  have h8 (q : Pattern) (selected : d232829 q = 1) : d236490 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d232829, d236490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232829, d236490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232830 q = 1) : d236491 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d232830, d236491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232830, d236491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232831 q = 1) : d236492 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d232831, d236492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232831, d236492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d233214 q = 1) : d236532 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d233214, d236532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233214, d236532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23486 q selected
  have h12 (q : Pattern) (selected : d233215 q = 1) : d236533 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d233215, d236533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233215, d236533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d233216 q = 1) : d236534 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d233216, d236534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233216, d236534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d233217 q = 1) : d236535 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d233217, d236535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233217, d236535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d233218 q = 1) : d236536 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d233218, d236536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d233218, d236536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d233219 q = 1) : d236537 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d233219, d236537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d233219, d236537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro23488 (p : Pattern) (selected : d233225 p = 1) : d236543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233220 q = 1) : d236538 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d233220, d236538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23487 q selected
    | true =>
      simp only [d233220, d236538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233221 q = 1) : d236539 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d233221, d236539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233221, d236539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233222 q = 1) : d236540 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d233222, d236540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233222, d236540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233223 q = 1) : d236541 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d233223, d236541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233223, d236541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233224 q = 1) : d236542 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d233224, d236542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233224, d236542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233225 q = 1) : d236543 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d233225, d236543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233225, d236543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23489 (p : Pattern) (selected : d233231 p = 1) : d236549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233226 q = 1) : d236544 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d233226, d236544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23488 q selected
    | true =>
      simp only [d233226, d236544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233227 q = 1) : d236545 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d233227, d236545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233227, d236545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233228 q = 1) : d236546 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d233228, d236546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233228, d236546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233229 q = 1) : d236547 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d233229, d236547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233229, d236547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233230 q = 1) : d236548 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d233230, d236548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233230, d236548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233231 q = 1) : d236549 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d233231, d236549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233231, d236549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23490 (p : Pattern) (selected : d233237 p = 1) : d236555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233232 q = 1) : d236550 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d233232, d236550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23489 q selected
    | true =>
      simp only [d233232, d236550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233233 q = 1) : d236551 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d233233, d236551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233233, d236551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233234 q = 1) : d236552 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d233234, d236552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233234, d236552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233235 q = 1) : d236553 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d233235, d236553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233235, d236553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233236 q = 1) : d236554 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d233236, d236554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233236, d236554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233237 q = 1) : d236555 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d233237, d236555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233237, d236555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23491 (p : Pattern) (selected : d233243 p = 1) : d236561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233238 q = 1) : d236556 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d233238, d236556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23490 q selected
    | true =>
      simp only [d233238, d236556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233239 q = 1) : d236557 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d233239, d236557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233239, d236557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233240 q = 1) : d236558 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d233240, d236558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233240, d236558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233241 q = 1) : d236559 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d233241, d236559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233241, d236559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233242 q = 1) : d236560 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d233242, d236560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233242, d236560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233243 q = 1) : d236561 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d233243, d236561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233243, d236561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23492 (p : Pattern) (selected : d233249 p = 1) : d236567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233244 q = 1) : d236562 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d233244, d236562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23491 q selected
    | true =>
      simp only [d233244, d236562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233245 q = 1) : d236563 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d233245, d236563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233245, d236563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233246 q = 1) : d236564 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d233246, d236564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233246, d236564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233247 q = 1) : d236565 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d233247, d236565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233247, d236565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233248 q = 1) : d236566 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d233248, d236566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233248, d236566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233249 q = 1) : d236567 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d233249, d236567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233249, d236567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23493 (p : Pattern) (selected : d233255 p = 1) : d236573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233250 q = 1) : d236568 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d233250, d236568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23492 q selected
    | true =>
      simp only [d233250, d236568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233251 q = 1) : d236569 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d233251, d236569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233251, d236569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233252 q = 1) : d236570 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d233252, d236570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233252, d236570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233253 q = 1) : d236571 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d233253, d236571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233253, d236571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233254 q = 1) : d236572 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d233254, d236572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233254, d236572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233255 q = 1) : d236573 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d233255, d236573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233255, d236573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23494 (p : Pattern) (selected : d233261 p = 1) : d236579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d233256 q = 1) : d236574 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d233256, d236574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23493 q selected
    | true =>
      simp only [d233256, d236574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d233257 q = 1) : d236575 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d233257, d236575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d233257, d236575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d233258 q = 1) : d236576 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d233258, d236576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d233258, d236576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d233259 q = 1) : d236577 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d233259, d236577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d233259, d236577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d233260 q = 1) : d236578 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d233260, d236578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d233260, d236578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d233261 q = 1) : d236579 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d233261, d236579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d233261, d236579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23495 (p : Pattern) (selected : d28739 p = 0) : d236584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d309 q = 0) : d52108 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d129 q = 0) : d51980 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d310 q = 0) : d52109 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d52109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d310, d52109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d534 q = 0) : d52281 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d52281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d534, d52281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d535 q = 0) : d52282 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d52282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d535, d52282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1519 q = 0) : d52960 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d1531 q = 0) : d52972 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d16 q = 0) : d51868 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d9579 q = 0) : d101159 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, d101159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9579, d101159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d28739 q = 0) : d236584 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28739, d236584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d28739, d236584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro23496 (p : Pattern) (selected : d28745 p = 0) : d236590 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d531 q = 0) : d52278 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d532 q = 0) : d52279 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d533 q = 0) : d52280 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d533, d52280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d28740 q = 0) : d236585 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d236585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23495 q selected
    | true =>
      simp only [d28740, d236585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d28741 q = 0) : d236586 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d236586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d28741, d236586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d28742 q = 0) : d236587 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d236587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28742, d236587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d28743 q = 0) : d236588 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d236588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d28743, d236588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d28744 q = 0) : d236589 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d236589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d28744, d236589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d315 q = 0) : d52114 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d316 q = 0) : d52115 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d317 q = 0) : d52116 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d28745 q = 0) : d236590 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28745, d236590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d28745, d236590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23497 (p : Pattern) (selected : d28750 p = 0) : d236595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315 q = 0) : d52114 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315, d52114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d316 q = 0) : d52115 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d316, d52115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d317 q = 0) : d52116 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d317, d52116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d5448 q = 0) : d74174 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d74174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d5448, d74174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d5449 q = 0) : d74175 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d74175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d5449, d74175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d28750 q = 0) : d236595 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28750, d236595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d28750, d236595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro23498 (p : Pattern) (selected : d28756 p = 0) : d236601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d28746 q = 0) : d236591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d236591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23496 q selected
    | true =>
      simp only [d28746, d236591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d28747 q = 0) : d236592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d236592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d28747, d236592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d28748 q = 0) : d236593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d236593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d28748, d236593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d28749 q = 0) : d236594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d236594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d28749, d236594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d28751 q = 0) : d236596 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d236596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23497 q selected
    | true =>
      simp only [d28751, d236596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d28752 q = 0) : d236597 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d236597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d28752, d236597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d28753 q = 0) : d236598 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d236598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d28753, d236598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28754 q = 0) : d236599 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d236599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28754, d236599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d28755 q = 0) : d236600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d236600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d28755, d236600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d23231 q = 0) : d208132 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d208132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19843 q selected
    | true =>
      simp only [d23231, d208132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d23232 q = 0) : d208133 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d208133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d23232, d208133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d23233 q = 0) : d208134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d208134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d23233, d208134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d23234 q = 0) : d208135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d208135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d23234, d208135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d12494 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d23235 q = 0) : d208136 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d208136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d23235, d208136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d28756 q = 0) : d236601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28756, d236601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d28756, d236601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro23499 (p : Pattern) (selected : d28762 p = 0) : d236607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d28757 q = 0) : d236602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28757, d236602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23498 q selected
    | true =>
      simp only [d28757, d236602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9863 q selected
  have h2 (q : Pattern) (selected : d28758 q = 0) : d236603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28758, d236603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d28758, d236603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d28759 q = 0) : d236604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28759, d236604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d28759, d236604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16082 q = 0) : d126990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d126990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9863 q selected
    | true =>
      simp only [d16082, d126990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9884 q selected
  have h5 (q : Pattern) (selected : d16083 q = 0) : d126991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d126991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16083, d126991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16084 q = 0) : d126992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d126992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16084, d126992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d28760 q = 0) : d236605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28760, d236605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d28760, d236605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d15967 q = 0) : d126875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9863 q selected
    | true =>
      simp only [d15967, d126875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h9 (q : Pattern) (selected : d15968 q = 0) : d126876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d126876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15968, d126876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15969 q = 0) : d126877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d126877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15969, d126877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d145 q = 0) : d51996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h12 (q : Pattern) (selected : d146 q = 0) : d51997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d147 q = 0) : d51998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d15970 q = 0) : d126878 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d126878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d15970, d126878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d28761 q = 0) : d236606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28761, d236606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28761, d236606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d28762 q = 0) : d236607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28762, d236607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d28762, d236607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
end NetHack.Soko22Hazard87
