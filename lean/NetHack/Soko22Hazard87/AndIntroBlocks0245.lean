import NetHack.Soko22Hazard87.AndIntroBlocks0244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro61250 (p : Pattern) (ha : d243692 p = 1) (hb : d245094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d244110 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d244110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60956 q ha hb
    | true =>
      simp only [d242306, d244110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61002 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d244333 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d244333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d244333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61055 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d244334 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d244334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d244334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d244584 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d244584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d244584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61117 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d244585 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d244585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d244585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d244586 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d244586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d244586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d244836 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d244836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d244836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61185 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d244837 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d244837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d244837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d244838 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d244838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d244838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d244839 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d244839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d244839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d245089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d245089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d245089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61249 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d245090 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d245090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d245090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d245091 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d245091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d245091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d245092 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d245092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d245092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d245093 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d245093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d245093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d245094 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d245094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d245094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro61251 (p : Pattern) (ha : d243698 p = 1) (hb : d245100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d245095 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d245095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61250 q ha hb
    | true =>
      simp only [d243693, d245095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d245096 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d245096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d245096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d245097 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d245097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d245097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d245098 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d245098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d245098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d245099 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d245099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d245099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d245100 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d245100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d245100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61252 (p : Pattern) (ha : d243704 p = 1) (hb : d245106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d245101 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d245101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61251 q ha hb
    | true =>
      simp only [d243699, d245101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d245102 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d245102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d245102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d245103 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d245103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d245103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d245104 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d245104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d245104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d245105 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d245105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d245105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d245106 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d245106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d245106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61253 (p : Pattern) (ha : d243710 p = 1) (hb : d245112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d245107 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d245107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61252 q ha hb
    | true =>
      simp only [d243705, d245107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d245108 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d245108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d245108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d245109 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d245109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d245109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d245110 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d245110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d245110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d245111 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d245111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d245111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d245112 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d245112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d245112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61254 (p : Pattern) (ha : d243716 p = 1) (hb : d245118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d245113 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d245113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61253 q ha hb
    | true =>
      simp only [d243711, d245113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d245114 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d245114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d245114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d245115 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d245115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d245115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d245116 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d245116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d245116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d245117 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d245117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d245117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d245118 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d245118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d245118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61255 (p : Pattern) (ha : d243722 p = 1) (hb : d245124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d245119 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d245119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61254 q ha hb
    | true =>
      simp only [d243717, d245119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d245120 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d245120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d245120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d245121 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d245121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d245121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d245122 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d245122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d245122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d245123 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d245123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d245123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d245124 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d245124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d245124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61256 (p : Pattern) (ha : d243728 p = 1) (hb : d245130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d245125 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d245125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61255 q ha hb
    | true =>
      simp only [d243723, d245125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d245126 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d245126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d245126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d245127 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d245127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d245127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d245128 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d245128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d245128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d245129 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d245129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d245129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d245130 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d245130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d245130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61257 (p : Pattern) (ha : d243734 p = 1) (hb : d245136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d245131 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d245131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61256 q ha hb
    | true =>
      simp only [d243729, d245131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d245132 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d245132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d245132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d245133 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d245133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d245133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d245134 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d245134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d245134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d245135 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d245135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d245135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d245136 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d245136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d245136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61258 (p : Pattern) (ha : d231169 p = 1) (hb : d241832 p = 1) : d245139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23154 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60617 q ha hb
    | true =>
      simp only [d23154, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23208 q = 1) (hb : d241832 q = 1) : d243808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23208, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23208, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23209 q = 1) (hb : d241832 q = 1) : d243809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23209, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23209, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23210 q = 1) (hb : d241832 q = 1) : d243810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23210, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23210, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23211 q = 1) (hb : d241832 q = 1) : d243811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23211, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23211, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231169 q = 1) (hb : d241832 q = 1) : d245139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231169, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231169, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61259 (p : Pattern) (ha : d231179 p = 1) (hb : d241832 p = 1) : d245149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d241832 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d23184 q = 1) (hb : d241832 q = 1) : d243784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23184, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60622 q ha hb
    | true =>
      simp only [d23184, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231175 q = 1) (hb : d241832 q = 1) : d245145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231175, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231175, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231176 q = 1) (hb : d241832 q = 1) : d245146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231176, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231176, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231177 q = 1) (hb : d241832 q = 1) : d245147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231177, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231177, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231178 q = 1) (hb : d241832 q = 1) : d245148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231178, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231178, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231179 q = 1) (hb : d241832 q = 1) : d245149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231179, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231179, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61260 (p : Pattern) (ha : d231185 p = 1) (hb : d241832 p = 1) : d245155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23213 q = 1) (hb : d241832 q = 1) : d243813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23213, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60625 q ha hb
    | true =>
      simp only [d23213, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60626 q ha hb
  have h2 (q : Pattern) (ha : d23214 q = 1) (hb : d241832 q = 1) : d243814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23214, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23214, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231167 q = 1) (hb : d241832 q = 1) : d245137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231167, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231167, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231168 q = 1) (hb : d241832 q = 1) : d245138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231168, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231168, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231170 q = 1) (hb : d241832 q = 1) : d245140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231170, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231170, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61258 q ha hb
  have h6 (q : Pattern) (ha : d231171 q = 1) (hb : d241832 q = 1) : d245141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231171, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231171, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231172 q = 1) (hb : d241832 q = 1) : d245142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231172, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231172, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231173 q = 1) (hb : d241832 q = 1) : d245143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231173, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231173, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231174 q = 1) (hb : d241832 q = 1) : d245144 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231174, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231174, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231180 q = 1) (hb : d241832 q = 1) : d245150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231180, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231180, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61259 q ha hb
  have h11 (q : Pattern) (ha : d231181 q = 1) (hb : d241832 q = 1) : d245151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231181, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231181, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231182 q = 1) (hb : d241832 q = 1) : d245152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231182, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231182, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231183 q = 1) (hb : d241832 q = 1) : d245153 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231183, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231183, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231184 q = 1) (hb : d241832 q = 1) : d245154 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231184, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231184, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231185 q = 1) (hb : d241832 q = 1) : d245155 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231185, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231185, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61261 (p : Pattern) (ha : d231191 p = 1) (hb : d241832 p = 1) : d245161 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d241832 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231186 q = 1) (hb : d241832 q = 1) : d245156 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231186, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231186, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61260 q ha hb
  have h3 (q : Pattern) (ha : d231187 q = 1) (hb : d241832 q = 1) : d245157 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231187, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231187, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231188 q = 1) (hb : d241832 q = 1) : d245158 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231188, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231188, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231189 q = 1) (hb : d241832 q = 1) : d245159 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231189, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231189, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231190 q = 1) (hb : d241832 q = 1) : d245160 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231190, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231190, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231191 q = 1) (hb : d241832 q = 1) : d245161 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231191, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231191, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61262 (p : Pattern) (ha : d231194 p = 1) (hb : d241832 p = 1) : d245164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23393 q = 1) (hb : d241832 q = 1) : d243950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23393, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60654 q ha hb
    | true =>
      simp only [d23393, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60655 q ha hb
  have h2 (q : Pattern) (ha : d23394 q = 1) (hb : d241832 q = 1) : d243951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23394, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23394, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23395 q = 1) (hb : d241832 q = 1) : d243952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23395, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23395, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23396 q = 1) (hb : d241832 q = 1) : d243953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23396, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23396, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23397 q = 1) (hb : d241832 q = 1) : d243954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23397, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23397, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231194 q = 1) (hb : d241832 q = 1) : d245164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231194, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231194, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61263 (p : Pattern) (ha : d231205 p = 1) (hb : d241832 p = 1) : d245175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231200 q = 1) (hb : d241832 q = 1) : d245170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231200, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60685 q ha hb
    | true =>
      simp only [d231200, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60661 q ha hb
  have h2 (q : Pattern) (ha : d231201 q = 1) (hb : d241832 q = 1) : d245171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231201, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231201, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231202 q = 1) (hb : d241832 q = 1) : d245172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231202, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231202, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231203 q = 1) (hb : d241832 q = 1) : d245173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231203, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231203, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231204 q = 1) (hb : d241832 q = 1) : d245174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231204, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231204, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231205 q = 1) (hb : d241832 q = 1) : d245175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231205, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231205, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61264 (p : Pattern) (ha : d231211 p = 1) (hb : d241832 p = 1) : d245181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23399 q = 1) (hb : d241832 q = 1) : d243956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23399, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60653 q ha hb
    | true =>
      simp only [d23399, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60656 q ha hb
  have h2 (q : Pattern) (ha : d23400 q = 1) (hb : d241832 q = 1) : d243957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23400, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23400, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231192 q = 1) (hb : d241832 q = 1) : d245162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231192, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231192, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231193 q = 1) (hb : d241832 q = 1) : d245163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231193, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231193, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231195 q = 1) (hb : d241832 q = 1) : d245165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231195, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231195, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61262 q ha hb
  have h6 (q : Pattern) (ha : d231196 q = 1) (hb : d241832 q = 1) : d245166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231196, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231196, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231197 q = 1) (hb : d241832 q = 1) : d245167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231197, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231197, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231198 q = 1) (hb : d241832 q = 1) : d245168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231198, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231198, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231199 q = 1) (hb : d241832 q = 1) : d245169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231199, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231199, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231206 q = 1) (hb : d241832 q = 1) : d245176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231206, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231206, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61263 q ha hb
  have h11 (q : Pattern) (ha : d231207 q = 1) (hb : d241832 q = 1) : d245177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231207, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231207, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231208 q = 1) (hb : d241832 q = 1) : d245178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231208, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231208, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231209 q = 1) (hb : d241832 q = 1) : d245179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231209, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231209, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231210 q = 1) (hb : d241832 q = 1) : d245180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231210, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231210, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231211 q = 1) (hb : d241832 q = 1) : d245181 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231211, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231211, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61265 (p : Pattern) (ha : d231217 p = 1) (hb : d241832 p = 1) : d245187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231212 q = 1) (hb : d241832 q = 1) : d245182 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231212, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231212, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61264 q ha hb
  have h2 (q : Pattern) (ha : d231213 q = 1) (hb : d241832 q = 1) : d245183 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231213, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231213, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231214 q = 1) (hb : d241832 q = 1) : d245184 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231214, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231214, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231215 q = 1) (hb : d241832 q = 1) : d245185 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231215, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231215, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231216 q = 1) (hb : d241832 q = 1) : d245186 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231216, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231216, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231217 q = 1) (hb : d241832 q = 1) : d245187 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231217, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231217, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61266 (p : Pattern) (ha : d231221 p = 1) (hb : d241832 p = 1) : d245191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23666 q = 1) (hb : d241832 q = 1) : d244155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23666, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60699 q ha hb
    | true =>
      simp only [d23666, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60700 q ha hb
  have h2 (q : Pattern) (ha : d23667 q = 1) (hb : d241832 q = 1) : d244156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23667, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23667, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23668 q = 1) (hb : d241832 q = 1) : d244157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23668, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23668, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23669 q = 1) (hb : d241832 q = 1) : d244158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23669, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23669, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23670 q = 1) (hb : d241832 q = 1) : d244159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23670, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23670, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231221 q = 1) (hb : d241832 q = 1) : d245191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231221, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231221, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61267 (p : Pattern) (ha : d231232 p = 1) (hb : d241832 p = 1) : d245202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231227 q = 1) (hb : d241832 q = 1) : d245197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231227, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60733 q ha hb
    | true =>
      simp only [d231227, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60708 q ha hb
  have h2 (q : Pattern) (ha : d231228 q = 1) (hb : d241832 q = 1) : d245198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231228, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231228, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231229 q = 1) (hb : d241832 q = 1) : d245199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231229, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231229, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231230 q = 1) (hb : d241832 q = 1) : d245200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231230, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231230, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231231 q = 1) (hb : d241832 q = 1) : d245201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231231, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231231, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231232 q = 1) (hb : d241832 q = 1) : d245202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231232, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231232, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61268 (p : Pattern) (ha : d231238 p = 1) (hb : d241832 p = 1) : d245208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23672 q = 1) (hb : d241832 q = 1) : d244161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23672, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60698 q ha hb
    | true =>
      simp only [d23672, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60701 q ha hb
  have h2 (q : Pattern) (ha : d23673 q = 1) (hb : d241832 q = 1) : d244162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23673, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23673, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231219 q = 1) (hb : d241832 q = 1) : d245189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231219, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231219, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231220 q = 1) (hb : d241832 q = 1) : d245190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231220, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231220, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231222 q = 1) (hb : d241832 q = 1) : d245192 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231222, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231222, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61266 q ha hb
  have h6 (q : Pattern) (ha : d231223 q = 1) (hb : d241832 q = 1) : d245193 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231223, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231223, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231224 q = 1) (hb : d241832 q = 1) : d245194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231224, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231224, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231225 q = 1) (hb : d241832 q = 1) : d245195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231225, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231225, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231226 q = 1) (hb : d241832 q = 1) : d245196 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231226, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231226, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231233 q = 1) (hb : d241832 q = 1) : d245203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231233, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231233, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61267 q ha hb
  have h11 (q : Pattern) (ha : d231234 q = 1) (hb : d241832 q = 1) : d245204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231234, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231234, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231235 q = 1) (hb : d241832 q = 1) : d245205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231235, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231235, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231236 q = 1) (hb : d241832 q = 1) : d245206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231236, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231236, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231237 q = 1) (hb : d241832 q = 1) : d245207 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231237, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231237, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231238 q = 1) (hb : d241832 q = 1) : d245208 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231238, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231238, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61269 (p : Pattern) (ha : d231244 p = 1) (hb : d241832 p = 1) : d245214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231239 q = 1) (hb : d241832 q = 1) : d245209 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231239, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231239, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61268 q ha hb
  have h2 (q : Pattern) (ha : d231240 q = 1) (hb : d241832 q = 1) : d245210 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231240, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231240, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231241 q = 1) (hb : d241832 q = 1) : d245211 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231241, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231241, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231242 q = 1) (hb : d241832 q = 1) : d245212 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231242, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231242, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231243 q = 1) (hb : d241832 q = 1) : d245213 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231243, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231243, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231244 q = 1) (hb : d241832 q = 1) : d245214 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231244, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231244, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61270 (p : Pattern) (ha : d231249 p = 1) (hb : d241832 p = 1) : d245219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23988 q = 1) (hb : d241832 q = 1) : d244379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23988, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60749 q ha hb
    | true =>
      simp only [d23988, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60750 q ha hb
  have h2 (q : Pattern) (ha : d23989 q = 1) (hb : d241832 q = 1) : d244380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23989, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23989, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23990 q = 1) (hb : d241832 q = 1) : d244381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d23990, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23990, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23991 q = 1) (hb : d241832 q = 1) : d244382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d23991, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23991, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23992 q = 1) (hb : d241832 q = 1) : d244383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d23992, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23992, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231249 q = 1) (hb : d241832 q = 1) : d245219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231249, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231249, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61271 (p : Pattern) (ha : d231260 p = 1) (hb : d241832 p = 1) : d245230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231255 q = 1) (hb : d241832 q = 1) : d245225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231255, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60787 q ha hb
    | true =>
      simp only [d231255, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60758 q ha hb
  have h2 (q : Pattern) (ha : d231256 q = 1) (hb : d241832 q = 1) : d245226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231256, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231256, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231257 q = 1) (hb : d241832 q = 1) : d245227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231257, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231257, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231258 q = 1) (hb : d241832 q = 1) : d245228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231258, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231258, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231259 q = 1) (hb : d241832 q = 1) : d245229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231259, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231259, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231260 q = 1) (hb : d241832 q = 1) : d245230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231260, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231260, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61272 (p : Pattern) (ha : d231266 p = 1) (hb : d241832 p = 1) : d245236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23994 q = 1) (hb : d241832 q = 1) : d244385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23994, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60748 q ha hb
    | true =>
      simp only [d23994, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60751 q ha hb
  have h2 (q : Pattern) (ha : d23995 q = 1) (hb : d241832 q = 1) : d244386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d23995, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23995, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231247 q = 1) (hb : d241832 q = 1) : d245217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231247, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231247, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231248 q = 1) (hb : d241832 q = 1) : d245218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231248, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231248, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231250 q = 1) (hb : d241832 q = 1) : d245220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231250, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231250, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61270 q ha hb
  have h6 (q : Pattern) (ha : d231251 q = 1) (hb : d241832 q = 1) : d245221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231251, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231251, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231252 q = 1) (hb : d241832 q = 1) : d245222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231252, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231252, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231253 q = 1) (hb : d241832 q = 1) : d245223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231253, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231253, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231254 q = 1) (hb : d241832 q = 1) : d245224 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231254, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231254, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231261 q = 1) (hb : d241832 q = 1) : d245231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231261, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231261, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61271 q ha hb
  have h11 (q : Pattern) (ha : d231262 q = 1) (hb : d241832 q = 1) : d245232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231262, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231262, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231263 q = 1) (hb : d241832 q = 1) : d245233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231263, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231263, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231264 q = 1) (hb : d241832 q = 1) : d245234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231264, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231264, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231265 q = 1) (hb : d241832 q = 1) : d245235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231265, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231265, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231266 q = 1) (hb : d241832 q = 1) : d245236 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231266, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231266, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61273 (p : Pattern) (ha : d231272 p = 1) (hb : d241832 p = 1) : d245242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231267 q = 1) (hb : d241832 q = 1) : d245237 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231267, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231267, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61272 q ha hb
  have h2 (q : Pattern) (ha : d231268 q = 1) (hb : d241832 q = 1) : d245238 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231268, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231268, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231269 q = 1) (hb : d241832 q = 1) : d245239 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231269, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231269, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231270 q = 1) (hb : d241832 q = 1) : d245240 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231270, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231270, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231271 q = 1) (hb : d241832 q = 1) : d245241 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231271, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231271, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231272 q = 1) (hb : d241832 q = 1) : d245242 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231272, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231272, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61274 (p : Pattern) (ha : d231278 p = 1) (hb : d241832 p = 1) : d245248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24370 q = 1) (hb : d241832 q = 1) : d244631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24370, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60806 q ha hb
    | true =>
      simp only [d24370, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60807 q ha hb
  have h2 (q : Pattern) (ha : d24371 q = 1) (hb : d241832 q = 1) : d244632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24371, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24371, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24372 q = 1) (hb : d241832 q = 1) : d244633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24372, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24372, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24373 q = 1) (hb : d241832 q = 1) : d244634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24373, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24373, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24374 q = 1) (hb : d241832 q = 1) : d244635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24374, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24374, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231278 q = 1) (hb : d241832 q = 1) : d245248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231278, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231278, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61275 (p : Pattern) (ha : d231289 p = 1) (hb : d241832 p = 1) : d245259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231284 q = 1) (hb : d241832 q = 1) : d245254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231284, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60844 q ha hb
    | true =>
      simp only [d231284, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60815 q ha hb
  have h2 (q : Pattern) (ha : d231285 q = 1) (hb : d241832 q = 1) : d245255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231285, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231285, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231286 q = 1) (hb : d241832 q = 1) : d245256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231286, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231286, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231287 q = 1) (hb : d241832 q = 1) : d245257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231287, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231287, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231288 q = 1) (hb : d241832 q = 1) : d245258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231288, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231288, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231289 q = 1) (hb : d241832 q = 1) : d245259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231289, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231289, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61276 (p : Pattern) (ha : d231295 p = 1) (hb : d241832 p = 1) : d245265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24376 q = 1) (hb : d241832 q = 1) : d244637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24376, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60805 q ha hb
    | true =>
      simp only [d24376, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60808 q ha hb
  have h2 (q : Pattern) (ha : d24377 q = 1) (hb : d241832 q = 1) : d244638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24377, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24377, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231276 q = 1) (hb : d241832 q = 1) : d245246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231276, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231276, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231277 q = 1) (hb : d241832 q = 1) : d245247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231277, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231277, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231279 q = 1) (hb : d241832 q = 1) : d245249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231279, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231279, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61274 q ha hb
  have h6 (q : Pattern) (ha : d231280 q = 1) (hb : d241832 q = 1) : d245250 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231280, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231280, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231281 q = 1) (hb : d241832 q = 1) : d245251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231281, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231281, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231282 q = 1) (hb : d241832 q = 1) : d245252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231282, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231282, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231283 q = 1) (hb : d241832 q = 1) : d245253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231283, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231283, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231290 q = 1) (hb : d241832 q = 1) : d245260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231290, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231290, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61275 q ha hb
  have h11 (q : Pattern) (ha : d231291 q = 1) (hb : d241832 q = 1) : d245261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231291, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231291, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231292 q = 1) (hb : d241832 q = 1) : d245262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231292, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231292, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231293 q = 1) (hb : d241832 q = 1) : d245263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231293, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231293, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231294 q = 1) (hb : d241832 q = 1) : d245264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231294, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231294, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231295 q = 1) (hb : d241832 q = 1) : d245265 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231295, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231295, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61277 (p : Pattern) (ha : d231301 p = 1) (hb : d241832 p = 1) : d245271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231296 q = 1) (hb : d241832 q = 1) : d245266 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231296, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231296, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61276 q ha hb
  have h2 (q : Pattern) (ha : d231297 q = 1) (hb : d241832 q = 1) : d245267 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231297, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231297, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231298 q = 1) (hb : d241832 q = 1) : d245268 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231298, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231298, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231299 q = 1) (hb : d241832 q = 1) : d245269 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231299, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231299, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231300 q = 1) (hb : d241832 q = 1) : d245270 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231300, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231300, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231301 q = 1) (hb : d241832 q = 1) : d245271 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231301, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231301, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61278 (p : Pattern) (ha : d231308 p = 1) (hb : d241832 p = 1) : d245278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24751 q = 1) (hb : d241832 q = 1) : d244884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d24751, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60863 q ha hb
    | true =>
      simp only [d24751, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60864 q ha hb
  have h2 (q : Pattern) (ha : d24752 q = 1) (hb : d241832 q = 1) : d244885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d24752, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24752, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d24753 q = 1) (hb : d241832 q = 1) : d244886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d24753, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d24753, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d24754 q = 1) (hb : d241832 q = 1) : d244887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d24754, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24754, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d24755 q = 1) (hb : d241832 q = 1) : d244888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d24755, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d24755, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231308 q = 1) (hb : d241832 q = 1) : d245278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231308, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231308, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61279 (p : Pattern) (ha : d231319 p = 1) (hb : d241832 p = 1) : d245289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231314 q = 1) (hb : d241832 q = 1) : d245284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231314, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60901 q ha hb
    | true =>
      simp only [d231314, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60872 q ha hb
  have h2 (q : Pattern) (ha : d231315 q = 1) (hb : d241832 q = 1) : d245285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231315, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231315, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231316 q = 1) (hb : d241832 q = 1) : d245286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231316, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231316, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231317 q = 1) (hb : d241832 q = 1) : d245287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231317, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231317, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231318 q = 1) (hb : d241832 q = 1) : d245288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231318, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231318, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231319 q = 1) (hb : d241832 q = 1) : d245289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231319, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231319, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61280 (p : Pattern) (ha : d231325 p = 1) (hb : d241832 p = 1) : d245295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d24757 q = 1) (hb : d241832 q = 1) : d244890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d24757, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60862 q ha hb
    | true =>
      simp only [d24757, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60865 q ha hb
  have h2 (q : Pattern) (ha : d24758 q = 1) (hb : d241832 q = 1) : d244891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d24758, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d24758, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231306 q = 1) (hb : d241832 q = 1) : d245276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231306, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231306, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231307 q = 1) (hb : d241832 q = 1) : d245277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231307, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231307, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231309 q = 1) (hb : d241832 q = 1) : d245279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231309, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231309, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61278 q ha hb
  have h6 (q : Pattern) (ha : d231310 q = 1) (hb : d241832 q = 1) : d245280 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231310, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231310, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d231311 q = 1) (hb : d241832 q = 1) : d245281 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231311, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231311, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d231312 q = 1) (hb : d241832 q = 1) : d245282 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231312, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d231312, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d231313 q = 1) (hb : d241832 q = 1) : d245283 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231313, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231313, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231320 q = 1) (hb : d241832 q = 1) : d245290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231320, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231320, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61279 q ha hb
  have h11 (q : Pattern) (ha : d231321 q = 1) (hb : d241832 q = 1) : d245291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231321, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231321, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d231322 q = 1) (hb : d241832 q = 1) : d245292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231322, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d231322, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d231323 q = 1) (hb : d241832 q = 1) : d245293 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231323, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d231323, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d231324 q = 1) (hb : d241832 q = 1) : d245294 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231324, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d231324, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d231325 q = 1) (hb : d241832 q = 1) : d245295 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231325, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d231325, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61281 (p : Pattern) (ha : d231331 p = 1) (hb : d241832 p = 1) : d245301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231326 q = 1) (hb : d241832 q = 1) : d245296 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231326, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231326, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61280 q ha hb
  have h2 (q : Pattern) (ha : d231327 q = 1) (hb : d241832 q = 1) : d245297 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231327, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231327, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d231328 q = 1) (hb : d241832 q = 1) : d245298 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231328, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231328, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231329 q = 1) (hb : d241832 q = 1) : d245299 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231329, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231329, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d231330 q = 1) (hb : d241832 q = 1) : d245300 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231330, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231330, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231331 q = 1) (hb : d241832 q = 1) : d245301 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231331, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231331, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61282 (p : Pattern) (ha : d231337 p = 1) (hb : d241832 p = 1) : d245307 p = 1 := by
  have h0 (q : Pattern) (ha : d231218 q = 1) (hb : d241832 q = 1) : d245188 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231218, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61261 q ha hb
    | true =>
      simp only [d231218, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61265 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d231245 q = 1) (hb : d241832 q = 1) : d245215 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231245, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231245, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61269 q ha hb
  have h3 (q : Pattern) (ha : d231246 q = 1) (hb : d241832 q = 1) : d245216 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231246, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d231246, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d231273 q = 1) (hb : d241832 q = 1) : d245243 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231273, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231273, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61273 q ha hb
  have h5 (q : Pattern) (ha : d231274 q = 1) (hb : d241832 q = 1) : d245244 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231274, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231274, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d231275 q = 1) (hb : d241832 q = 1) : d245245 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231275, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231275, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d231302 q = 1) (hb : d241832 q = 1) : d245272 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231302, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231302, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61277 q ha hb
  have h8 (q : Pattern) (ha : d231303 q = 1) (hb : d241832 q = 1) : d245273 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231303, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231303, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d231304 q = 1) (hb : d241832 q = 1) : d245274 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231304, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231304, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d231305 q = 1) (hb : d241832 q = 1) : d245275 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231305, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d231305, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d231332 q = 1) (hb : d241832 q = 1) : d245302 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d231332, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231332, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61281 q ha hb
  have h12 (q : Pattern) (ha : d231333 q = 1) (hb : d241832 q = 1) : d245303 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d231333, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231333, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d231334 q = 1) (hb : d241832 q = 1) : d245304 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d231334, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231334, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d231335 q = 1) (hb : d241832 q = 1) : d245305 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d231335, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231335, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d231336 q = 1) (hb : d241832 q = 1) : d245306 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d231336, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d231336, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d231337 q = 1) (hb : d241832 q = 1) : d245307 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d231337, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d231337, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro61283 (p : Pattern) (ha : d231343 p = 1) (hb : d241832 p = 1) : d245313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231338 q = 1) (hb : d241832 q = 1) : d245308 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d231338, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61282 q ha hb
    | true =>
      simp only [d231338, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231339 q = 1) (hb : d241832 q = 1) : d245309 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d231339, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231339, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231340 q = 1) (hb : d241832 q = 1) : d245310 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d231340, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231340, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231341 q = 1) (hb : d241832 q = 1) : d245311 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d231341, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231341, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231342 q = 1) (hb : d241832 q = 1) : d245312 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d231342, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231342, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231343 q = 1) (hb : d241832 q = 1) : d245313 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d231343, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231343, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61284 (p : Pattern) (ha : d231349 p = 1) (hb : d241832 p = 1) : d245319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231344 q = 1) (hb : d241832 q = 1) : d245314 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d231344, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61283 q ha hb
    | true =>
      simp only [d231344, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231345 q = 1) (hb : d241832 q = 1) : d245315 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d231345, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231345, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231346 q = 1) (hb : d241832 q = 1) : d245316 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d231346, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231346, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231347 q = 1) (hb : d241832 q = 1) : d245317 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d231347, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231347, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231348 q = 1) (hb : d241832 q = 1) : d245318 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d231348, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231348, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231349 q = 1) (hb : d241832 q = 1) : d245319 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d231349, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231349, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61285 (p : Pattern) (ha : d231355 p = 1) (hb : d241832 p = 1) : d245325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231350 q = 1) (hb : d241832 q = 1) : d245320 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d231350, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61284 q ha hb
    | true =>
      simp only [d231350, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231351 q = 1) (hb : d241832 q = 1) : d245321 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d231351, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231351, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231352 q = 1) (hb : d241832 q = 1) : d245322 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d231352, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231352, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231353 q = 1) (hb : d241832 q = 1) : d245323 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d231353, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231353, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231354 q = 1) (hb : d241832 q = 1) : d245324 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d231354, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231354, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231355 q = 1) (hb : d241832 q = 1) : d245325 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d231355, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231355, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61286 (p : Pattern) (ha : d231361 p = 1) (hb : d241832 p = 1) : d245331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231356 q = 1) (hb : d241832 q = 1) : d245326 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d231356, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61285 q ha hb
    | true =>
      simp only [d231356, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231357 q = 1) (hb : d241832 q = 1) : d245327 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d231357, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231357, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231358 q = 1) (hb : d241832 q = 1) : d245328 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d231358, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231358, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231359 q = 1) (hb : d241832 q = 1) : d245329 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d231359, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231359, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231360 q = 1) (hb : d241832 q = 1) : d245330 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d231360, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231360, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231361 q = 1) (hb : d241832 q = 1) : d245331 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d231361, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231361, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61287 (p : Pattern) (ha : d231367 p = 1) (hb : d241832 p = 1) : d245337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231362 q = 1) (hb : d241832 q = 1) : d245332 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d231362, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61286 q ha hb
    | true =>
      simp only [d231362, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231363 q = 1) (hb : d241832 q = 1) : d245333 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d231363, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231363, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231364 q = 1) (hb : d241832 q = 1) : d245334 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d231364, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231364, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231365 q = 1) (hb : d241832 q = 1) : d245335 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d231365, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231365, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231366 q = 1) (hb : d241832 q = 1) : d245336 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d231366, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231366, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231367 q = 1) (hb : d241832 q = 1) : d245337 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d231367, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231367, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61288 (p : Pattern) (ha : d231373 p = 1) (hb : d241832 p = 1) : d245343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231368 q = 1) (hb : d241832 q = 1) : d245338 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d231368, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61287 q ha hb
    | true =>
      simp only [d231368, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231369 q = 1) (hb : d241832 q = 1) : d245339 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d231369, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231369, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231370 q = 1) (hb : d241832 q = 1) : d245340 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d231370, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231370, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231371 q = 1) (hb : d241832 q = 1) : d245341 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d231371, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231371, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231372 q = 1) (hb : d241832 q = 1) : d245342 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d231372, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231372, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231373 q = 1) (hb : d241832 q = 1) : d245343 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d231373, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231373, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61289 (p : Pattern) (ha : d231379 p = 1) (hb : d241832 p = 1) : d245349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d231374 q = 1) (hb : d241832 q = 1) : d245344 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d231374, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61288 q ha hb
    | true =>
      simp only [d231374, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d231375 q = 1) (hb : d241832 q = 1) : d245345 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d231375, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d231375, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d231376 q = 1) (hb : d241832 q = 1) : d245346 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d231376, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231376, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d231377 q = 1) (hb : d241832 q = 1) : d245347 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d231377, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d231377, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d231378 q = 1) (hb : d241832 q = 1) : d245348 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d231378, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d231378, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d231379 q = 1) (hb : d241832 q = 1) : d245349 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d231379, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d231379, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61290 (p : Pattern) (ha : d104 p = 1) (hb : d241860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241855 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d241856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d241856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d241856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d241857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d241857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d241857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d241858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d241858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d241858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d241859 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d241859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d241859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d241860 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d241860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d241860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61291 (p : Pattern) (ha : d111 p = 1) (hb : d241867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241855 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d241856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d241856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d241856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d241857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d241857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d241857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d241858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d241858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d241858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d241859 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d241859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d241859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d241862 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d107 q = 1) (hb : d241863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d241863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107, d241863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108 q = 1) (hb : d241864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d241864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108, d241864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109 q = 1) (hb : d241865 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d241865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109, d241865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d110 q = 1) (hb : d241866 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d241866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d110, d241866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d111 q = 1) (hb : d241867 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d241867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d111, d241867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61292 (p : Pattern) (ha : d406 p = 1) (hb : d241874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241862 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d241863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d241863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d241863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d241864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d241864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d241864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d241872 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d241872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d241872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d241873 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d241873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d241873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d241874 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d241874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d241874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61293 (p : Pattern) (ha : d462 p = 1) (hb : d241903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241898 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d241899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d241899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d241899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d241900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d241900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d241900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d241901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d241901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d241901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d241902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d241902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d241902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d241903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d241903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d241903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61294 (p : Pattern) (ha : d53647 p = 1) (hb : d241909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d241868 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d241868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61290 q ha hb
    | true =>
      simp only [d112, d241868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61291 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d241869 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d241869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d241869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d241870 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d241870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d241870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d241871 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d241871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d241871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d241875 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d241875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d241875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61292 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d241876 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d241876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d241876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d241877 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d241877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d241877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d241878 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d241878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d241878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d241879 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d241879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d241879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d241904 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d241904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d241904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61293 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d241905 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d241905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d241905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d241906 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d241906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d241906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d241907 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d241907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d241907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d241908 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d241908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d241908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d241909 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d241909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d241909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro61295 (p : Pattern) (ha : d241986 p = 1) (hb : d243805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d241855 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60921 q ha hb
    | true =>
      simp only [d241855, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d241976 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d241976, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241983 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241983, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241984 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241984, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241985 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241985, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241986 q = 1) (hb : d243805 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d241986, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241986, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61296 (p : Pattern) (ha : d242005 p = 1) (hb : d243812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d241855 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241855, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60921 q ha hb
    | true =>
      simp only [d241855, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d241976 q = 1) (hb : d243801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241976, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d241976, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d241983 q = 1) (hb : d243802 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d241983, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241983, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d241984 q = 1) (hb : d243803 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d241984, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241984, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241985 q = 1) (hb : d243804 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d241985, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d241985, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d241862 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60923 q ha hb
    | true =>
      simp only [d241862, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d241998 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d241998, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242002 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242002, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242003 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242003, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242003, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242004 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242004, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242004, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242005 q = 1) (hb : d243812 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242005, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242005, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61297 (p : Pattern) (ha : d242014 p = 1) (hb : d245139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241997 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241862 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241862, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60923 q ha hb
    | true =>
      simp only [d241862, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d241998 q = 1) (hb : d243808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d241998, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d241998, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242002 q = 1) (hb : d243809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242002, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242002, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242012 q = 1) (hb : d243810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242012, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242012, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242013 q = 1) (hb : d243811 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242013, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242013, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242014 q = 1) (hb : d245139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242014, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242014, d245139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61298 (p : Pattern) (ha : d242054 p = 1) (hb : d245149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241898 q = 1) (hb : d243784 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d241898, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60928 q ha hb
    | true =>
      simp only [d241898, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d242044 q = 1) (hb : d245145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242044, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242044, d245145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242051 q = 1) (hb : d245146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242051, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242051, d245146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242052 q = 1) (hb : d245147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242052, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242052, d245147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242053 q = 1) (hb : d245148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242053, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242053, d245148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242054 q = 1) (hb : d245149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242054, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242054, d245149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61299 (p : Pattern) (ha : d242060 p = 1) (hb : d245155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242006 q = 1) (hb : d243813 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242006, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61295 q ha hb
    | true =>
      simp only [d242006, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61296 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242009 q = 1) (hb : d243814 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242009, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242009, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242010 q = 1) (hb : d245137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242010, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242010, d245137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242011 q = 1) (hb : d245138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242011, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242011, d245138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242015 q = 1) (hb : d245140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242015, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242015, d245140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61297 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242016 q = 1) (hb : d245141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242016, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242016, d245141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242017 q = 1) (hb : d245142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242017, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242017, d245142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242018 q = 1) (hb : d245143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242018, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242018, d245143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242019 q = 1) (hb : d245144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242019, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242019, d245144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242055 q = 1) (hb : d245150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242055, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242055, d245150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61298 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242056 q = 1) (hb : d245151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242056, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242056, d245151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242057 q = 1) (hb : d245152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242057, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242057, d245152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242058 q = 1) (hb : d245153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242058, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242058, d245153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242059 q = 1) (hb : d245154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242059, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242059, d245154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242060 q = 1) (hb : d245155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242060, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242060, d245155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61300 (p : Pattern) (ha : d242066 p = 1) (hb : d245161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d241910 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d241910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61294 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d241911 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d241911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d241912 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d241912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d241913 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d241913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d241914 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d241914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242061 q = 1) (hb : d245156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242061, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242061, d245156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61299 q ha hb
  have h8 (q : Pattern) (ha : d242062 q = 1) (hb : d245157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242062, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242062, d245157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242063 q = 1) (hb : d245158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242063, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242063, d245158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242064 q = 1) (hb : d245159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242064, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242064, d245159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d242065 q = 1) (hb : d245160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242065, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242065, d245160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d242066 q = 1) (hb : d245161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242066, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d242066, d245161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro61301 (p : Pattern) (ha : d242177 p = 1) (hb : d243945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242084 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60959 q ha hb
    | true =>
      simp only [d242084, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60960 q ha hb
  have h5 (q : Pattern) (ha : d242167 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242167, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242174 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242174, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242175 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242175, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242176 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242176, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242177 q = 1) (hb : d243945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242177, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242177, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61302 (p : Pattern) (ha : d242198 p = 1) (hb : d243955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242084 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242084, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60959 q ha hb
    | true =>
      simp only [d242084, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60960 q ha hb
  have h4 (q : Pattern) (ha : d242167 q = 1) (hb : d243941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242167, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242167, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242173 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242174 q = 1) (hb : d243942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242174, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242174, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242175 q = 1) (hb : d243943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242175, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242175, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242176 q = 1) (hb : d243944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242176, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242176, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242183 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242094 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60962 q ha hb
    | true =>
      simp only [d242094, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60963 q ha hb
  have h13 (q : Pattern) (ha : d242191 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242191, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242195 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242195, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242196 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242196, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242196, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242197 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242197, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242197, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242198 q = 1) (hb : d243955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242198, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242198, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61303 (p : Pattern) (ha : d242218 p = 1) (hb : d245164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242094 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242094, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60962 q ha hb
    | true =>
      simp only [d242094, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60963 q ha hb
  have h3 (q : Pattern) (ha : d242191 q = 1) (hb : d243951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242191, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242191, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242195 q = 1) (hb : d243952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242195, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242195, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242216 q = 1) (hb : d243953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242216, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242216, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242217 q = 1) (hb : d243954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242217, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242217, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242218 q = 1) (hb : d245164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242218, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242218, d245164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61304 (p : Pattern) (ha : d242286 p = 1) (hb : d245175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242275 q = 1) (hb : d245170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242275, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60996 q ha hb
    | true =>
      simp only [d242275, d245170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60999 q ha hb
  have h3 (q : Pattern) (ha : d242276 q = 1) (hb : d245171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242276, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242276, d245171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242282 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242283 q = 1) (hb : d245172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242283, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242283, d245172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242284 q = 1) (hb : d245173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242284, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242284, d245173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242285 q = 1) (hb : d245174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242285, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242285, d245174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242286 q = 1) (hb : d245175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242286, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242286, d245175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61305 (p : Pattern) (ha : d242299 p = 1) (hb : d245181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242199 q = 1) (hb : d243956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242199, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61301 q ha hb
    | true =>
      simp only [d242199, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61302 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242213 q = 1) (hb : d243957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242213, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242213, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242214 q = 1) (hb : d245162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242214, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242214, d245162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242215 q = 1) (hb : d245163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242215, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242215, d245163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242219 q = 1) (hb : d245165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242219, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242219, d245165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61303 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242221 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242222 q = 1) (hb : d245166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242222, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242222, d245166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242223 q = 1) (hb : d245167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242223, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242223, d245167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242224 q = 1) (hb : d245168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242224, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242224, d245168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242225 q = 1) (hb : d245169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242225, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242225, d245169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242287 q = 1) (hb : d245176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242287, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242287, d245176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61304 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242294 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242295 q = 1) (hb : d245177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242295, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242295, d245177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242296 q = 1) (hb : d245178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242296, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242296, d245178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242297 q = 1) (hb : d245179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242297, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242297, d245179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242298 q = 1) (hb : d245180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242298, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242298, d245180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242299 q = 1) (hb : d245181 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242299, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242299, d245181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61306 (p : Pattern) (ha : d242305 p = 1) (hb : d245187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242300 q = 1) (hb : d245182 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242300, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242300, d245182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61305 q ha hb
  have h2 (q : Pattern) (ha : d242301 q = 1) (hb : d245183 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242301, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242301, d245183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242302 q = 1) (hb : d245184 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242302, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242302, d245184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242303 q = 1) (hb : d245185 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242303, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242303, d245185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242304 q = 1) (hb : d245186 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242304, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242304, d245186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242305 q = 1) (hb : d245187 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242305, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242305, d245187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61307 (p : Pattern) (ha : d242435 p = 1) (hb : d244150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242342 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61009 q ha hb
    | true =>
      simp only [d242342, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61010 q ha hb
  have h5 (q : Pattern) (ha : d242425 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242425, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242432 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242432, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242433 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242433, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242434 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242434, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242435 q = 1) (hb : d244150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242435, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242435, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61308 (p : Pattern) (ha : d242456 p = 1) (hb : d244160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242368 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242424 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242342 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242342, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61009 q ha hb
    | true =>
      simp only [d242342, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61010 q ha hb
  have h4 (q : Pattern) (ha : d242425 q = 1) (hb : d244146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242425, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242425, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242432 q = 1) (hb : d244147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242432, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242432, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242433 q = 1) (hb : d244148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242433, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242433, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242434 q = 1) (hb : d244149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242434, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242434, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242352 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61012 q ha hb
    | true =>
      simp only [d242352, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61013 q ha hb
  have h13 (q : Pattern) (ha : d242449 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242449, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242453 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242453, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242454 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242454, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242454, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242455 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242455, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242455, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242456 q = 1) (hb : d244160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242456, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242456, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61309 (p : Pattern) (ha : d242476 p = 1) (hb : d245191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242352 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242352, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61012 q ha hb
    | true =>
      simp only [d242352, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61013 q ha hb
  have h3 (q : Pattern) (ha : d242449 q = 1) (hb : d244156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242449, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242449, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242453 q = 1) (hb : d244157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242453, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242453, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242474 q = 1) (hb : d244158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242474, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242474, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242475 q = 1) (hb : d244159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242475, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242475, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242476 q = 1) (hb : d245191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242476, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242476, d245191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61310 (p : Pattern) (ha : d242561 p = 1) (hb : d245202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242550 q = 1) (hb : d245197 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242550, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61049 q ha hb
    | true =>
      simp only [d242550, d245197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61052 q ha hb
  have h3 (q : Pattern) (ha : d242551 q = 1) (hb : d245198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242551, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242551, d245198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242558 q = 1) (hb : d245199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242558, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242558, d245199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242559 q = 1) (hb : d245200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242559, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242559, d245200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242560 q = 1) (hb : d245201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242560, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242560, d245201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242561 q = 1) (hb : d245202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242561, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242561, d245202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61311 (p : Pattern) (ha : d242574 p = 1) (hb : d245208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242360 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242457 q = 1) (hb : d244161 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242457, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61307 q ha hb
    | true =>
      simp only [d242457, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61308 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242471 q = 1) (hb : d244162 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242471, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242471, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242472 q = 1) (hb : d245189 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242472, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242472, d245189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242473 q = 1) (hb : d245190 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242473, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242473, d245190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242477 q = 1) (hb : d245192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242477, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242477, d245192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61309 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242479 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242480 q = 1) (hb : d245193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242480, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242480, d245193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242481 q = 1) (hb : d245194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242481, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242481, d245194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242482 q = 1) (hb : d245195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242482, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242482, d245195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242483 q = 1) (hb : d245196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242483, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242483, d245196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242562 q = 1) (hb : d245203 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242562, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242562, d245203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61310 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242570 q = 1) (hb : d245204 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242570, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242570, d245204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242571 q = 1) (hb : d245205 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242571, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242571, d245205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242572 q = 1) (hb : d245206 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242572, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242572, d245206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242573 q = 1) (hb : d245207 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242573, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242573, d245207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242574 q = 1) (hb : d245208 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242574, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242574, d245208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61312 (p : Pattern) (ha : d242580 p = 1) (hb : d245214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242575 q = 1) (hb : d245209 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242575, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242575, d245209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61311 q ha hb
  have h2 (q : Pattern) (ha : d242576 q = 1) (hb : d245210 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242576, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242576, d245210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242577 q = 1) (hb : d245211 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242577, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242577, d245211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242578 q = 1) (hb : d245212 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242578, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242578, d245212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242579 q = 1) (hb : d245213 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242579, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242579, d245213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242580 q = 1) (hb : d245214 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242580, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242580, d245214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61313 (p : Pattern) (ha : d242768 p = 1) (hb : d244374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d242662 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61067 q ha hb
    | true =>
      simp only [d242662, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61068 q ha hb
  have h5 (q : Pattern) (ha : d242749 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d242749, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d242765 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242765, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d242766 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242766, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d242767 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242767, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d242768 q = 1) (hb : d244374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242768, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242768, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61314 (p : Pattern) (ha : d242789 p = 1) (hb : d244384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242662 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242662, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61067 q ha hb
    | true =>
      simp only [d242662, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61068 q ha hb
  have h4 (q : Pattern) (ha : d242749 q = 1) (hb : d244370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242749, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d242749, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d242764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d242765 q = 1) (hb : d244371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242765, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d242765, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d242766 q = 1) (hb : d244372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242766, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242766, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242767 q = 1) (hb : d244373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242767, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242767, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d242774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d242779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d242672 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61070 q ha hb
    | true =>
      simp only [d242672, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61071 q ha hb
  have h13 (q : Pattern) (ha : d242782 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d242782, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242786 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242786, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242787 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242787, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d242787, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d242788 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242788, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d242788, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d242789 q = 1) (hb : d244384 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242789, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d242789, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61315 (p : Pattern) (ha : d242809 p = 1) (hb : d245219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242672 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242672, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61070 q ha hb
    | true =>
      simp only [d242672, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61071 q ha hb
  have h3 (q : Pattern) (ha : d242782 q = 1) (hb : d244380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242782, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242782, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242786 q = 1) (hb : d244381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242786, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242786, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242807 q = 1) (hb : d244382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242807, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242807, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242808 q = 1) (hb : d244383 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242808, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242808, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242809 q = 1) (hb : d245219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242809, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242809, d245219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61316 (p : Pattern) (ha : d242930 p = 1) (hb : d245230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d242905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242910 q = 1) (hb : d245225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d242910, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61109 q ha hb
    | true =>
      simp only [d242910, d245225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61114 q ha hb
  have h3 (q : Pattern) (ha : d242911 q = 1) (hb : d245226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d242911, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242911, d245226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d242926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242927 q = 1) (hb : d245227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d242927, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242927, d245227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242928 q = 1) (hb : d245228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d242928, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242928, d245228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242929 q = 1) (hb : d245229 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d242929, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242929, d245229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d242930 q = 1) (hb : d245230 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d242930, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242930, d245230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61317 (p : Pattern) (ha : d242943 p = 1) (hb : d245236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d242680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242790 q = 1) (hb : d244385 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242790, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61313 q ha hb
    | true =>
      simp only [d242790, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61314 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d242803 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d242804 q = 1) (hb : d244386 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242804, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d242804, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d242805 q = 1) (hb : d245217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242805, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242805, d245217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d242806 q = 1) (hb : d245218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242806, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242806, d245218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d242810 q = 1) (hb : d245220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242810, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242810, d245220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61315 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d242812 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d242813 q = 1) (hb : d245221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242813, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d242813, d245221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d242814 q = 1) (hb : d245222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242814, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d242814, d245222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d242815 q = 1) (hb : d245223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242815, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d242815, d245223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d242816 q = 1) (hb : d245224 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242816, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242816, d245224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d242931 q = 1) (hb : d245231 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d242931, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d242931, d245231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61316 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d242938 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d242939 q = 1) (hb : d245232 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d242939, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d242939, d245232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d242940 q = 1) (hb : d245233 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d242940, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d242940, d245233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d242941 q = 1) (hb : d245234 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d242941, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d242941, d245234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d242942 q = 1) (hb : d245235 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d242942, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d242942, d245235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d242943 q = 1) (hb : d245236 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d242943, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d242943, d245236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61318 (p : Pattern) (ha : d242949 p = 1) (hb : d245242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d242944 q = 1) (hb : d245237 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d242944, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242944, d245237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61317 q ha hb
  have h2 (q : Pattern) (ha : d242945 q = 1) (hb : d245238 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d242945, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242945, d245238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d242946 q = 1) (hb : d245239 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d242946, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242946, d245239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242947 q = 1) (hb : d245240 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d242947, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242947, d245240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d242948 q = 1) (hb : d245241 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d242948, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242948, d245241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242949 q = 1) (hb : d245242 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d242949, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d242949, d245242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61319 (p : Pattern) (ha : d243151 p = 1) (hb : d244626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243045 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61132 q ha hb
    | true =>
      simp only [d243045, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61133 q ha hb
  have h5 (q : Pattern) (ha : d243119 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243119, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243148 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243148, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243149 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243149, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243150 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243150, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243151 q = 1) (hb : d244626 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243151, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243151, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61320 (p : Pattern) (ha : d243172 p = 1) (hb : d244636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243045 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243045, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61132 q ha hb
    | true =>
      simp only [d243045, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61133 q ha hb
  have h4 (q : Pattern) (ha : d243119 q = 1) (hb : d244622 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243119, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243119, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243148 q = 1) (hb : d244623 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243148, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243148, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243149 q = 1) (hb : d244624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243149, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243149, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243150 q = 1) (hb : d244625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243150, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243150, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243162 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243055 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61135 q ha hb
    | true =>
      simp only [d243055, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61136 q ha hb
  have h13 (q : Pattern) (ha : d243165 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243165, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243169 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243169, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243170 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243170, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243170, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243171 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243171, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243171, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243172 q = 1) (hb : d244636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243172, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243172, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61321 (p : Pattern) (ha : d243192 p = 1) (hb : d245248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243164 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243055 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243055, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61135 q ha hb
    | true =>
      simp only [d243055, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61136 q ha hb
  have h3 (q : Pattern) (ha : d243165 q = 1) (hb : d244632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243165, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243165, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243169 q = 1) (hb : d244633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243169, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243169, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243190 q = 1) (hb : d244634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243190, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243190, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243191 q = 1) (hb : d244635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243191, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243191, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243192 q = 1) (hb : d245248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243192, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243192, d245248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61322 (p : Pattern) (ha : d243320 p = 1) (hb : d245259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243289 q = 1) (hb : d245254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243289, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61176 q ha hb
    | true =>
      simp only [d243289, d245254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61182 q ha hb
  have h3 (q : Pattern) (ha : d243290 q = 1) (hb : d245255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243290, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243290, d245255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243317 q = 1) (hb : d245256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243317, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243317, d245256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243318 q = 1) (hb : d245257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243318, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243318, d245257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243319 q = 1) (hb : d245258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243319, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243319, d245258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243320 q = 1) (hb : d245259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243320, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243320, d245259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61323 (p : Pattern) (ha : d243333 p = 1) (hb : d245265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243173 q = 1) (hb : d244637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243173, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61319 q ha hb
    | true =>
      simp only [d243173, d244637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61320 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243187 q = 1) (hb : d244638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243187, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243187, d244638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243188 q = 1) (hb : d245246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243188, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243188, d245246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243189 q = 1) (hb : d245247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243189, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243189, d245247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243193 q = 1) (hb : d245249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243193, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243193, d245249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61321 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243196 q = 1) (hb : d245250 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243196, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243196, d245250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243197 q = 1) (hb : d245251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243197, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243197, d245251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243198 q = 1) (hb : d245252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243198, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243198, d245252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243199 q = 1) (hb : d245253 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243199, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243199, d245253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243321 q = 1) (hb : d245260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243321, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243321, d245260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61322 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243329 q = 1) (hb : d245261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243329, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243329, d245261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243330 q = 1) (hb : d245262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243330, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243330, d245262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243331 q = 1) (hb : d245263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243331, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243331, d245263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243332 q = 1) (hb : d245264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243332, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243332, d245264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243333 q = 1) (hb : d245265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243333, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243333, d245265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61324 (p : Pattern) (ha : d243339 p = 1) (hb : d245271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243334 q = 1) (hb : d245266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243334, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243334, d245266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61323 q ha hb
  have h2 (q : Pattern) (ha : d243335 q = 1) (hb : d245267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243335, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243335, d245267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243336 q = 1) (hb : d245268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243336, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243336, d245268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243337 q = 1) (hb : d245269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243337, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243337, d245269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243338 q = 1) (hb : d245270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243338, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243338, d245270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243339 q = 1) (hb : d245271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243339, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243339, d245271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61325 (p : Pattern) (ha : d243516 p = 1) (hb : d244879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243423 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61199 q ha hb
    | true =>
      simp only [d243423, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61200 q ha hb
  have h5 (q : Pattern) (ha : d243478 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d243478, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243513 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243513, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d243514 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243514, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243515 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243515, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243516 q = 1) (hb : d244879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243516, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243516, d244879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61326 (p : Pattern) (ha : d243537 p = 1) (hb : d244889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243423 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243423, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61199 q ha hb
    | true =>
      simp only [d243423, d244874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61200 q ha hb
  have h4 (q : Pattern) (ha : d243478 q = 1) (hb : d244875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243478, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d243478, d244875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d243512 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243513 q = 1) (hb : d244876 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243513, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243513, d244876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d243514 q = 1) (hb : d244877 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243514, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243514, d244877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243515 q = 1) (hb : d244878 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243515, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243515, d244878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d243522 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d243527 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d243433 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61202 q ha hb
    | true =>
      simp only [d243433, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61203 q ha hb
  have h13 (q : Pattern) (ha : d243530 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d243530, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243534 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243534, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243535 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243535, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d243535, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243536 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243536, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d243536, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243537 q = 1) (hb : d244889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243537, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243537, d244889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61327 (p : Pattern) (ha : d243557 p = 1) (hb : d245278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243433 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243433, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61202 q ha hb
    | true =>
      simp only [d243433, d244884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61203 q ha hb
  have h3 (q : Pattern) (ha : d243530 q = 1) (hb : d244885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243530, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243530, d244885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243534 q = 1) (hb : d244886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243534, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243534, d244886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243555 q = 1) (hb : d244887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243555, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243555, d244887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243556 q = 1) (hb : d244888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243556, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243556, d244888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243557 q = 1) (hb : d245278 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243557, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243557, d245278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61328 (p : Pattern) (ha : d243667 p = 1) (hb : d245289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d243631 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d243636 q = 1) (hb : d245284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d243636, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61240 q ha hb
    | true =>
      simp only [d243636, d245284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61246 q ha hb
  have h3 (q : Pattern) (ha : d243637 q = 1) (hb : d245285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243637, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243637, d245285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243664 q = 1) (hb : d245286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243664, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243664, d245286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243665 q = 1) (hb : d245287 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243665, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243665, d245287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243666 q = 1) (hb : d245288 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243666, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243666, d245288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243667 q = 1) (hb : d245289 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243667, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243667, d245289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61329 (p : Pattern) (ha : d243680 p = 1) (hb : d245295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d243441 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243538 q = 1) (hb : d244890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243538, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61325 q ha hb
    | true =>
      simp only [d243538, d244890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61326 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243552 q = 1) (hb : d244891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243552, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243552, d244891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243553 q = 1) (hb : d245276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243553, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243553, d245276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d243554 q = 1) (hb : d245277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243554, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243554, d245277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243558 q = 1) (hb : d245279 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243558, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243558, d245279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61327 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d243560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d243561 q = 1) (hb : d245280 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243561, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243561, d245280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d243562 q = 1) (hb : d245281 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243562, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243562, d245281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d243563 q = 1) (hb : d245282 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243563, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243563, d245282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d243564 q = 1) (hb : d245283 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243564, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243564, d245283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243668 q = 1) (hb : d245290 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243668, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d243668, d245290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61328 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d243675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243676 q = 1) (hb : d245291 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243676, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243676, d245291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d243677 q = 1) (hb : d245292 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d243677, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243677, d245292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d243678 q = 1) (hb : d245293 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d243678, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d243678, d245293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d243679 q = 1) (hb : d245294 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d243679, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d243679, d245294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d243680 q = 1) (hb : d245295 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d243680, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d243680, d245295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61330 (p : Pattern) (ha : d243686 p = 1) (hb : d245301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243681 q = 1) (hb : d245296 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d243681, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243681, d245296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61329 q ha hb
  have h2 (q : Pattern) (ha : d243682 q = 1) (hb : d245297 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d243682, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243682, d245297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d243683 q = 1) (hb : d245298 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d243683, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243683, d245298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d243684 q = 1) (hb : d245299 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d243684, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243684, d245299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d243685 q = 1) (hb : d245300 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d243685, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243685, d245300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243686 q = 1) (hb : d245301 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d243686, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d243686, d245301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61331 (p : Pattern) (ha : d243692 p = 1) (hb : d245307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d242306 q = 1) (hb : d245188 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242306, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61300 q ha hb
    | true =>
      simp only [d242306, d245188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61306 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d242581 q = 1) (hb : d245215 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242581, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242581, d245215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61312 q ha hb
  have h3 (q : Pattern) (ha : d242582 q = 1) (hb : d245216 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242582, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d242582, d245216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d242950 q = 1) (hb : d245243 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d242950, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242950, d245243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61318 q ha hb
  have h5 (q : Pattern) (ha : d242951 q = 1) (hb : d245244 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d242951, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d242951, d245244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d242952 q = 1) (hb : d245245 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d242952, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d242952, d245245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243340 q = 1) (hb : d245272 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243340, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243340, d245272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61324 q ha hb
  have h8 (q : Pattern) (ha : d243341 q = 1) (hb : d245273 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243341, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243341, d245273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243342 q = 1) (hb : d245274 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243342, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243342, d245274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243343 q = 1) (hb : d245275 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243343, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243343, d245275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d243687 q = 1) (hb : d245302 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d243687, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243687, d245302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61330 q ha hb
  have h12 (q : Pattern) (ha : d243688 q = 1) (hb : d245303 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d243688, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243688, d245303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d243689 q = 1) (hb : d245304 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d243689, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243689, d245304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d243690 q = 1) (hb : d245305 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d243690, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d243690, d245305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d243691 q = 1) (hb : d245306 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d243691, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243691, d245306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243692 q = 1) (hb : d245307 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d243692, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d243692, d245307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro61332 (p : Pattern) (ha : d243698 p = 1) (hb : d245313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243693 q = 1) (hb : d245308 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d243693, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61331 q ha hb
    | true =>
      simp only [d243693, d245308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243694 q = 1) (hb : d245309 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d243694, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243694, d245309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243695 q = 1) (hb : d245310 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d243695, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243695, d245310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243696 q = 1) (hb : d245311 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d243696, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243696, d245311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243697 q = 1) (hb : d245312 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d243697, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243697, d245312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243698 q = 1) (hb : d245313 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d243698, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243698, d245313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61333 (p : Pattern) (ha : d243704 p = 1) (hb : d245319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243699 q = 1) (hb : d245314 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d243699, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61332 q ha hb
    | true =>
      simp only [d243699, d245314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243700 q = 1) (hb : d245315 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d243700, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243700, d245315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243701 q = 1) (hb : d245316 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d243701, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243701, d245316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243702 q = 1) (hb : d245317 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d243702, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243702, d245317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243703 q = 1) (hb : d245318 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d243703, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243703, d245318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243704 q = 1) (hb : d245319 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d243704, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243704, d245319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61334 (p : Pattern) (ha : d243710 p = 1) (hb : d245325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243705 q = 1) (hb : d245320 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d243705, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61333 q ha hb
    | true =>
      simp only [d243705, d245320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243706 q = 1) (hb : d245321 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d243706, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243706, d245321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243707 q = 1) (hb : d245322 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d243707, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243707, d245322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243708 q = 1) (hb : d245323 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d243708, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243708, d245323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243709 q = 1) (hb : d245324 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d243709, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243709, d245324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243710 q = 1) (hb : d245325 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d243710, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243710, d245325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61335 (p : Pattern) (ha : d243716 p = 1) (hb : d245331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243711 q = 1) (hb : d245326 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d243711, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61334 q ha hb
    | true =>
      simp only [d243711, d245326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243712 q = 1) (hb : d245327 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d243712, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243712, d245327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243713 q = 1) (hb : d245328 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d243713, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243713, d245328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243714 q = 1) (hb : d245329 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d243714, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243714, d245329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243715 q = 1) (hb : d245330 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d243715, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243715, d245330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243716 q = 1) (hb : d245331 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d243716, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243716, d245331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61336 (p : Pattern) (ha : d243722 p = 1) (hb : d245337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243717 q = 1) (hb : d245332 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d243717, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61335 q ha hb
    | true =>
      simp only [d243717, d245332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243718 q = 1) (hb : d245333 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d243718, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243718, d245333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243719 q = 1) (hb : d245334 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d243719, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243719, d245334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243720 q = 1) (hb : d245335 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d243720, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243720, d245335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243721 q = 1) (hb : d245336 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d243721, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243721, d245336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243722 q = 1) (hb : d245337 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d243722, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243722, d245337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61337 (p : Pattern) (ha : d243728 p = 1) (hb : d245343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243723 q = 1) (hb : d245338 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d243723, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61336 q ha hb
    | true =>
      simp only [d243723, d245338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243724 q = 1) (hb : d245339 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d243724, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243724, d245339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243725 q = 1) (hb : d245340 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d243725, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243725, d245340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243726 q = 1) (hb : d245341 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d243726, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243726, d245341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243727 q = 1) (hb : d245342 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d243727, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243727, d245342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243728 q = 1) (hb : d245343 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d243728, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243728, d245343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61338 (p : Pattern) (ha : d243734 p = 1) (hb : d245349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243729 q = 1) (hb : d245344 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d243729, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61337 q ha hb
    | true =>
      simp only [d243729, d245344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d243730 q = 1) (hb : d245345 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d243730, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243730, d245345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d243731 q = 1) (hb : d245346 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d243731, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243731, d245346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d243732 q = 1) (hb : d245347 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d243732, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243732, d245347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d243733 q = 1) (hb : d245348 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d243733, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243733, d245348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d243734 q = 1) (hb : d245349 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d243734, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243734, d245349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro61339 (p : Pattern) (ha : d104 p = 1) (hb : d245354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30657 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d245350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d245351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d245352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d245353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d245354 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d245354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d245354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61340 (p : Pattern) (ha : d111 p = 1) (hb : d245359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d245350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d245350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d245351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d245351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d245352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d245352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d245353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d245353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30664 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d245355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d245356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d245357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d245357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d245357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d245358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d245358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d245358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d245359 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d245359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d245359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61341 (p : Pattern) (ha : d406 p = 1) (hb : d245366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d245355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d245355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d245356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d245356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d245364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d245364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d245364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d245365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d245365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d245365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d245366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d245366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d245366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61342 (p : Pattern) (ha : d462 p = 1) (hb : d245376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30700 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d245372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d245372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d245372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d245373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d245373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d245373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d245374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d245374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d245374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d245375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d245375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d245375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d245376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d245376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d245376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61343 (p : Pattern) (ha : d53647 p = 1) (hb : d245382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d245360 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d245360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61339 q ha hb
    | true =>
      simp only [d112, d245360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61340 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d245361 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d245361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d245361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d245362 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d245362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d245362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d245363 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d245363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d245363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d245367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d245367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d245367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61341 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d245368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d245368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d245368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d245369 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d245369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d245369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d245370 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d245370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d245370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d245371 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d245371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d245371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d245377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d245377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d245377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61342 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d245378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d245378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d245378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d245379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d245379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d245379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d245380 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d245380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d245380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d245381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d245381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d245381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d245382 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d245382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d245382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro61344 (p : Pattern) (ha : d243805 p = 1) (hb : d245392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243801 q = 1) (hb : d245388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243801, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243801, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243802 q = 1) (hb : d245389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243802, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243802, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243803 q = 1) (hb : d245390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243803, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243803, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243804 q = 1) (hb : d245391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243804, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243804, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243805 q = 1) (hb : d245392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243805, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243805, d245392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61345 (p : Pattern) (ha : d243812 p = 1) (hb : d245397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30737 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243801 q = 1) (hb : d245388 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243801, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243801, d245388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243802 q = 1) (hb : d245389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243802, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243802, d245389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243803 q = 1) (hb : d245390 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243803, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243803, d245390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243804 q = 1) (hb : d245391 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243804, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243804, d245391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d243808 q = 1) (hb : d245393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243808, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243808, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243809 q = 1) (hb : d245394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243809, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243809, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243810 q = 1) (hb : d245395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243810, d245395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243810, d245395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243811 q = 1) (hb : d245396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243811, d245396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243811, d245396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243812 q = 1) (hb : d245397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243812, d245397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243812, d245397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61346 (p : Pattern) (ha : d245139 p = 1) (hb : d245404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243808 q = 1) (hb : d245393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243808, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243808, d245393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30828 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243809 q = 1) (hb : d245394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243809, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243809, d245394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243810 q = 1) (hb : d245402 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243810, d245402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243810, d245402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243811 q = 1) (hb : d245403 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243811, d245403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243811, d245403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245139 q = 1) (hb : d245404 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245139, d245404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245139, d245404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61347 (p : Pattern) (ha : d245149 p = 1) (hb : d245414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245145 q = 1) (hb : d245410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245145, d245410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245145, d245410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245146 q = 1) (hb : d245411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245146, d245411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245146, d245411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245147 q = 1) (hb : d245412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245147, d245412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245147, d245412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245148 q = 1) (hb : d245413 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245148, d245413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245148, d245413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245149 q = 1) (hb : d245414 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245149, d245414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245149, d245414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61348 (p : Pattern) (ha : d245155 p = 1) (hb : d245420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243813 q = 1) (hb : d245398 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243813, d245398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61344 q ha hb
    | true =>
      simp only [d243813, d245398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61345 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243814 q = 1) (hb : d245399 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243814, d245399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243814, d245399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245137 q = 1) (hb : d245400 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245137, d245400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245137, d245400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245138 q = 1) (hb : d245401 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245138, d245401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245138, d245401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245140 q = 1) (hb : d245405 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245140, d245405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245140, d245405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61346 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245141 q = 1) (hb : d245406 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245141, d245406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245141, d245406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245142 q = 1) (hb : d245407 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245142, d245407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245142, d245407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245143 q = 1) (hb : d245408 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245143, d245408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245143, d245408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245144 q = 1) (hb : d245409 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245144, d245409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245144, d245409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245150 q = 1) (hb : d245415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245150, d245415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245150, d245415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61347 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245151 q = 1) (hb : d245416 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245151, d245416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245151, d245416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245152 q = 1) (hb : d245417 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245152, d245417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245152, d245417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245153 q = 1) (hb : d245418 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245153, d245418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245153, d245418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245154 q = 1) (hb : d245419 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245154, d245419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245154, d245419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245155 q = 1) (hb : d245420 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245155, d245420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245155, d245420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61349 (p : Pattern) (ha : d245161 p = 1) (hb : d245426 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d245156 q = 1) (hb : d245421 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245156, d245421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245156, d245421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61348 q ha hb
  have h8 (q : Pattern) (ha : d245157 q = 1) (hb : d245422 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245157, d245422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245157, d245422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245158 q = 1) (hb : d245423 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245158, d245423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245158, d245423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245159 q = 1) (hb : d245424 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245159, d245424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245159, d245424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245160 q = 1) (hb : d245425 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245160, d245425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245160, d245425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245161 q = 1) (hb : d245426 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245161, d245426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245161, d245426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro61350 (p : Pattern) (ha : d243945 p = 1) (hb : d245431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243941 q = 1) (hb : d245427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243941, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243941, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d243942 q = 1) (hb : d245428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243942, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d243942, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243943 q = 1) (hb : d245429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243943, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243943, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d243944 q = 1) (hb : d245430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243944, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243944, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d243945 q = 1) (hb : d245431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243945, d245431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243945, d245431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61351 (p : Pattern) (ha : d243955 p = 1) (hb : d245436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d243940 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d243941 q = 1) (hb : d245427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243941, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d243941, d245427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31062 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d243942 q = 1) (hb : d245428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243942, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d243942, d245428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243943 q = 1) (hb : d245429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243943, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243943, d245429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d243944 q = 1) (hb : d245430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243944, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243944, d245430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31072 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31077 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d243951 q = 1) (hb : d245432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243951, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d243951, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d243952 q = 1) (hb : d245433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243952, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d243952, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d243953 q = 1) (hb : d245434 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243953, d245434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d243953, d245434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d243954 q = 1) (hb : d245435 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243954, d245435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d243954, d245435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d243955 q = 1) (hb : d245436 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d243955, d245436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d243955, d245436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61352 (p : Pattern) (ha : d245164 p = 1) (hb : d245443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31079 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243950 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243951 q = 1) (hb : d245432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d243951, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243951, d245432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d243952 q = 1) (hb : d245433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d243952, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d243952, d245433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d243953 q = 1) (hb : d245441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d243953, d245441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243953, d245441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d243954 q = 1) (hb : d245442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d243954, d245442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d243954, d245442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245164 q = 1) (hb : d245443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245164, d245443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245164, d245443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61353 (p : Pattern) (ha : d245175 p = 1) (hb : d245453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245170 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245171 q = 1) (hb : d245449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245171, d245449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245171, d245449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31202 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245172 q = 1) (hb : d245450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245172, d245450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245172, d245450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245173 q = 1) (hb : d245451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245173, d245451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245173, d245451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245174 q = 1) (hb : d245452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245174, d245452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245174, d245452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245175 q = 1) (hb : d245453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245175, d245453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245175, d245453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61354 (p : Pattern) (ha : d245181 p = 1) (hb : d245459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d243956 q = 1) (hb : d245437 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d243956, d245437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61350 q ha hb
    | true =>
      simp only [d243956, d245437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61351 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d243957 q = 1) (hb : d245438 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d243957, d245438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d243957, d245438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245162 q = 1) (hb : d245439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245162, d245439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245162, d245439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245163 q = 1) (hb : d245440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245163, d245440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245163, d245440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245165 q = 1) (hb : d245444 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245165, d245444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245165, d245444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61352 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31113 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245166 q = 1) (hb : d245445 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245166, d245445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245166, d245445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245167 q = 1) (hb : d245446 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245167, d245446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245167, d245446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245168 q = 1) (hb : d245447 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245168, d245447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245168, d245447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245169 q = 1) (hb : d245448 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245169, d245448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245169, d245448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245176 q = 1) (hb : d245454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245176, d245454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245176, d245454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61353 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245177 q = 1) (hb : d245455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245177, d245455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245177, d245455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245178 q = 1) (hb : d245456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245178, d245456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245178, d245456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245179 q = 1) (hb : d245457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245179, d245457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245179, d245457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245180 q = 1) (hb : d245458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245180, d245458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245180, d245458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245181 q = 1) (hb : d245459 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245181, d245459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245181, d245459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61355 (p : Pattern) (ha : d245187 p = 1) (hb : d245465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245182 q = 1) (hb : d245460 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245182, d245460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245182, d245460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61354 q ha hb
  have h2 (q : Pattern) (ha : d245183 q = 1) (hb : d245461 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245183, d245461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245183, d245461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245184 q = 1) (hb : d245462 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245184, d245462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245184, d245462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245185 q = 1) (hb : d245463 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245185, d245463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245185, d245463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245186 q = 1) (hb : d245464 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245186, d245464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245186, d245464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245187 q = 1) (hb : d245465 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245187, d245465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245187, d245465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61356 (p : Pattern) (ha : d244150 p = 1) (hb : d245471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244146 q = 1) (hb : d245467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244146, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244146, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d244147 q = 1) (hb : d245468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244147, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d244147, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244148 q = 1) (hb : d245469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244148, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244148, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d244149 q = 1) (hb : d245470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244149, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244149, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d244150 q = 1) (hb : d245471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244150, d245471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244150, d245471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61357 (p : Pattern) (ha : d244160 p = 1) (hb : d245476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31292 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31348 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d244146 q = 1) (hb : d245467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244146, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244146, d245467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d244147 q = 1) (hb : d245468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244147, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d244147, d245468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244148 q = 1) (hb : d245469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244148, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244148, d245469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244149 q = 1) (hb : d245470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244149, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244149, d245470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d244156 q = 1) (hb : d245472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244156, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d244156, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d244157 q = 1) (hb : d245473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244157, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d244157, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d244158 q = 1) (hb : d245474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244158, d245474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d244158, d245474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d244159 q = 1) (hb : d245475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244159, d245475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d244159, d245475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d244160 q = 1) (hb : d245476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244160, d245476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d244160, d245476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61358 (p : Pattern) (ha : d245191 p = 1) (hb : d245483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31436 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244156 q = 1) (hb : d245472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244156, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244156, d245472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244157 q = 1) (hb : d245473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244157, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244157, d245473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d244158 q = 1) (hb : d245481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244158, d245481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244158, d245481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244159 q = 1) (hb : d245482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244159, d245482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244159, d245482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245191 q = 1) (hb : d245483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245191, d245483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245191, d245483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61359 (p : Pattern) (ha : d245202 p = 1) (hb : d245493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245197 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245198 q = 1) (hb : d245489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245198, d245489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245198, d245489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31591 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245199 q = 1) (hb : d245490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245199, d245490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245199, d245490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245200 q = 1) (hb : d245491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245200, d245491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245200, d245491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245201 q = 1) (hb : d245492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245201, d245492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245201, d245492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245202 q = 1) (hb : d245493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245202, d245493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245202, d245493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61360 (p : Pattern) (ha : d245208 p = 1) (hb : d245499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244161 q = 1) (hb : d245477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d244161, d245477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61356 q ha hb
    | true =>
      simp only [d244161, d245477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61357 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31461 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244162 q = 1) (hb : d245478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d244162, d245478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244162, d245478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245189 q = 1) (hb : d245479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245189, d245479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245189, d245479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245190 q = 1) (hb : d245480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245190, d245480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245190, d245480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245192 q = 1) (hb : d245484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245192, d245484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245192, d245484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61358 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31470 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245193 q = 1) (hb : d245485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245193, d245485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245193, d245485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245194 q = 1) (hb : d245486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245194, d245486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245194, d245486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245195 q = 1) (hb : d245487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245195, d245487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245195, d245487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245196 q = 1) (hb : d245488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245196, d245488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245196, d245488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245203 q = 1) (hb : d245494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245203, d245494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245203, d245494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61359 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31607 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245204 q = 1) (hb : d245495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245204, d245495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245204, d245495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245205 q = 1) (hb : d245496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245205, d245496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245205, d245496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245206 q = 1) (hb : d245497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245206, d245497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245206, d245497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245207 q = 1) (hb : d245498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245207, d245498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245207, d245498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245208 q = 1) (hb : d245499 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245208, d245499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245208, d245499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61361 (p : Pattern) (ha : d245214 p = 1) (hb : d245505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245209 q = 1) (hb : d245500 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245209, d245500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245209, d245500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61360 q ha hb
  have h2 (q : Pattern) (ha : d245210 q = 1) (hb : d245501 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245210, d245501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245210, d245501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245211 q = 1) (hb : d245502 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245211, d245502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245211, d245502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245212 q = 1) (hb : d245503 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245212, d245503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245212, d245503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245213 q = 1) (hb : d245504 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245213, d245504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245213, d245504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245214 q = 1) (hb : d245505 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245214, d245505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245214, d245505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61362 (p : Pattern) (ha : d244374 p = 1) (hb : d245512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244370 q = 1) (hb : d245508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244370, d245508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244370, d245508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d244371 q = 1) (hb : d245509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244371, d245509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d244371, d245509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244372 q = 1) (hb : d245510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244372, d245510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244372, d245510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d244373 q = 1) (hb : d245511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244373, d245511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244373, d245511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d244374 q = 1) (hb : d245512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244374, d245512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244374, d245512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61363 (p : Pattern) (ha : d244384 p = 1) (hb : d245517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244369 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d244370 q = 1) (hb : d245508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244370, d245508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244370, d245508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d31892 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d244371 q = 1) (hb : d245509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244371, d245509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d244371, d245509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244372 q = 1) (hb : d245510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244372, d245510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244372, d245510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244373 q = 1) (hb : d245511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244373, d245511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244373, d245511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d31902 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d31907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d244380 q = 1) (hb : d245513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244380, d245513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d244380, d245513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d244381 q = 1) (hb : d245514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244381, d245514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d244381, d245514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d244382 q = 1) (hb : d245515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244382, d245515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d244382, d245515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d244383 q = 1) (hb : d245516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244383, d245516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d244383, d245516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d244384 q = 1) (hb : d245517 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244384, d245517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d244384, d245517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61364 (p : Pattern) (ha : d245219 p = 1) (hb : d245524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244380 q = 1) (hb : d245513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244380, d245513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244380, d245513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d31916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244381 q = 1) (hb : d245514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244381, d245514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244381, d245514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d244382 q = 1) (hb : d245522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244382, d245522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244382, d245522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244383 q = 1) (hb : d245523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244383, d245523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244383, d245523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245219 q = 1) (hb : d245524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245219, d245524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245219, d245524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61365 (p : Pattern) (ha : d245230 p = 1) (hb : d245534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245226 q = 1) (hb : d245530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245226, d245530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245226, d245530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245227 q = 1) (hb : d245531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245227, d245531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245227, d245531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245228 q = 1) (hb : d245532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245228, d245532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245228, d245532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245229 q = 1) (hb : d245533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245229, d245533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245229, d245533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245230 q = 1) (hb : d245534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245230, d245534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245230, d245534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61366 (p : Pattern) (ha : d245236 p = 1) (hb : d245540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d31718 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244385 q = 1) (hb : d245518 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d244385, d245518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61362 q ha hb
    | true =>
      simp only [d244385, d245518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61363 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244386 q = 1) (hb : d245519 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d244386, d245519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244386, d245519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245217 q = 1) (hb : d245520 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245217, d245520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245217, d245520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245218 q = 1) (hb : d245521 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245218, d245521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245218, d245521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245220 q = 1) (hb : d245525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245220, d245525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245220, d245525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61364 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31943 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245221 q = 1) (hb : d245526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245221, d245526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245221, d245526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245222 q = 1) (hb : d245527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245222, d245527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245222, d245527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245223 q = 1) (hb : d245528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245223, d245528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245223, d245528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245224 q = 1) (hb : d245529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245224, d245529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245224, d245529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245231 q = 1) (hb : d245535 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245231, d245535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245231, d245535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61365 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32125 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245232 q = 1) (hb : d245536 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245232, d245536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245232, d245536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245233 q = 1) (hb : d245537 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245233, d245537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245233, d245537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245234 q = 1) (hb : d245538 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245234, d245538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245234, d245538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245235 q = 1) (hb : d245539 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245235, d245539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245235, d245539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245236 q = 1) (hb : d245540 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245236, d245540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245236, d245540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61367 (p : Pattern) (ha : d245242 p = 1) (hb : d245546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245237 q = 1) (hb : d245541 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245237, d245541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245237, d245541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61366 q ha hb
  have h2 (q : Pattern) (ha : d245238 q = 1) (hb : d245542 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245238, d245542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245238, d245542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245239 q = 1) (hb : d245543 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245239, d245543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245239, d245543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245240 q = 1) (hb : d245544 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245240, d245544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245240, d245544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245241 q = 1) (hb : d245545 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245241, d245545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245241, d245545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245242 q = 1) (hb : d245546 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245242, d245546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245242, d245546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61368 (p : Pattern) (ha : d244626 p = 1) (hb : d245554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244622 q = 1) (hb : d245550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244622, d245550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244622, d245550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d244623 q = 1) (hb : d245551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244623, d245551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d244623, d245551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244624 q = 1) (hb : d245552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244624, d245552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244624, d245552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d244625 q = 1) (hb : d245553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244625, d245553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244625, d245553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d244626 q = 1) (hb : d245554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244626, d245554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244626, d245554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61369 (p : Pattern) (ha : d244636 p = 1) (hb : d245559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244621 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d244622 q = 1) (hb : d245550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244622, d245550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244622, d245550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d244623 q = 1) (hb : d245551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244623, d245551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d244623, d245551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244624 q = 1) (hb : d245552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244624, d245552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244624, d245552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244625 q = 1) (hb : d245553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244625, d245553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244625, d245553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d244632 q = 1) (hb : d245555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244632, d245555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d244632, d245555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d244633 q = 1) (hb : d245556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244633, d245556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d244633, d245556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d244634 q = 1) (hb : d245557 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244634, d245557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d244634, d245557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d244635 q = 1) (hb : d245558 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244635, d245558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d244635, d245558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d244636 q = 1) (hb : d245559 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244636, d245559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d244636, d245559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61370 (p : Pattern) (ha : d245248 p = 1) (hb : d245566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244631 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244632 q = 1) (hb : d245555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244632, d245555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244632, d245555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244633 q = 1) (hb : d245556 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244633, d245556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244633, d245556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d244634 q = 1) (hb : d245564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244634, d245564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244634, d245564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244635 q = 1) (hb : d245565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244635, d245565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244635, d245565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245248 q = 1) (hb : d245566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245248, d245566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245248, d245566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61371 (p : Pattern) (ha : d245259 p = 1) (hb : d245576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245255 q = 1) (hb : d245572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245255, d245572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245255, d245572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32655 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245256 q = 1) (hb : d245573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245256, d245573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245256, d245573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245257 q = 1) (hb : d245574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245257, d245574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245257, d245574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245258 q = 1) (hb : d245575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245258, d245575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245258, d245575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245259 q = 1) (hb : d245576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245259, d245576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245259, d245576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61372 (p : Pattern) (ha : d245265 p = 1) (hb : d245582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244637 q = 1) (hb : d245560 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d244637, d245560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61368 q ha hb
    | true =>
      simp only [d244637, d245560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61369 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244638 q = 1) (hb : d245561 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d244638, d245561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244638, d245561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245246 q = 1) (hb : d245562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245246, d245562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245246, d245562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245247 q = 1) (hb : d245563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245247, d245563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245247, d245563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245249 q = 1) (hb : d245567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245249, d245567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245249, d245567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61370 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245250 q = 1) (hb : d245568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245250, d245568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245250, d245568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245251 q = 1) (hb : d245569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245251, d245569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245251, d245569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245252 q = 1) (hb : d245570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245252, d245570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245252, d245570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245253 q = 1) (hb : d245571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245253, d245571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245253, d245571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245260 q = 1) (hb : d245577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245260, d245577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245260, d245577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61371 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32671 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245261 q = 1) (hb : d245578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245261, d245578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245261, d245578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245262 q = 1) (hb : d245579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245262, d245579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245262, d245579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245263 q = 1) (hb : d245580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245263, d245580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245263, d245580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245264 q = 1) (hb : d245581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245264, d245581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245264, d245581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245265 q = 1) (hb : d245582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245265, d245582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245265, d245582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61373 (p : Pattern) (ha : d245271 p = 1) (hb : d245588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245266 q = 1) (hb : d245583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245266, d245583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245266, d245583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61372 q ha hb
  have h2 (q : Pattern) (ha : d245267 q = 1) (hb : d245584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245267, d245584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245267, d245584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245268 q = 1) (hb : d245585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245268, d245585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245268, d245585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245269 q = 1) (hb : d245586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245269, d245586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245269, d245586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245270 q = 1) (hb : d245587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245270, d245587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245270, d245587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245271 q = 1) (hb : d245588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245271, d245588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245271, d245588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61374 (p : Pattern) (ha : d244879 p = 1) (hb : d245597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244875 q = 1) (hb : d245593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244875, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244875, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d244876 q = 1) (hb : d245594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244876, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d244876, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244877 q = 1) (hb : d245595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244877, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244877, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d244878 q = 1) (hb : d245596 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244878, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244878, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d244879 q = 1) (hb : d245597 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244879, d245597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244879, d245597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61375 (p : Pattern) (ha : d244889 p = 1) (hb : d245602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d244874 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d244875 q = 1) (hb : d245593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244875, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d244875, d245593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d32935 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d244876 q = 1) (hb : d245594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244876, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d244876, d245594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244877 q = 1) (hb : d245595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244877, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244877, d245595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d244878 q = 1) (hb : d245596 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244878, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244878, d245596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32945 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32950 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d244885 q = 1) (hb : d245598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244885, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d244885, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d244886 q = 1) (hb : d245599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244886, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d244886, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d244887 q = 1) (hb : d245600 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244887, d245600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d244887, d245600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d244888 q = 1) (hb : d245601 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244888, d245601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d244888, d245601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d244889 q = 1) (hb : d245602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d244889, d245602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d244889, d245602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro61376 (p : Pattern) (ha : d245278 p = 1) (hb : d245609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244885 q = 1) (hb : d245598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d244885, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244885, d245598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d32959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d244886 q = 1) (hb : d245599 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d244886, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d244886, d245599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d244887 q = 1) (hb : d245607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d244887, d245607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244887, d245607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d244888 q = 1) (hb : d245608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d244888, d245608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d244888, d245608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245278 q = 1) (hb : d245609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245278, d245609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245278, d245609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61377 (p : Pattern) (ha : d245289 p = 1) (hb : d245619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245285 q = 1) (hb : d245615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245285, d245615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245285, d245615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245286 q = 1) (hb : d245616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245286, d245616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245286, d245616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245287 q = 1) (hb : d245617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245287, d245617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245287, d245617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245288 q = 1) (hb : d245618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245288, d245618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245288, d245618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245289 q = 1) (hb : d245619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245289, d245619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245289, d245619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61378 (p : Pattern) (ha : d245295 p = 1) (hb : d245625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d32784 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244890 q = 1) (hb : d245603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d244890, d245603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61374 q ha hb
    | true =>
      simp only [d244890, d245603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61375 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244891 q = 1) (hb : d245604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d244891, d245604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d244891, d245604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245276 q = 1) (hb : d245605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245276, d245605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245276, d245605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245277 q = 1) (hb : d245606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245277, d245606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245277, d245606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245279 q = 1) (hb : d245610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245279, d245610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245279, d245610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61376 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d32986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d245280 q = 1) (hb : d245611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245280, d245611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245280, d245611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245281 q = 1) (hb : d245612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245281, d245612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245281, d245612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245282 q = 1) (hb : d245613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245282, d245613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245282, d245613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d245283 q = 1) (hb : d245614 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245283, d245614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245283, d245614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245290 q = 1) (hb : d245620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245290, d245620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245290, d245620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61377 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d245291 q = 1) (hb : d245621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245291, d245621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245291, d245621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245292 q = 1) (hb : d245622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245292, d245622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245292, d245622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245293 q = 1) (hb : d245623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245293, d245623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245293, d245623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d245294 q = 1) (hb : d245624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245294, d245624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245294, d245624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d245295 q = 1) (hb : d245625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245295, d245625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245295, d245625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61379 (p : Pattern) (ha : d245301 p = 1) (hb : d245631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245296 q = 1) (hb : d245626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245296, d245626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245296, d245626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61378 q ha hb
  have h2 (q : Pattern) (ha : d245297 q = 1) (hb : d245627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245297, d245627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245297, d245627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245298 q = 1) (hb : d245628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245298, d245628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245298, d245628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245299 q = 1) (hb : d245629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245299, d245629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245299, d245629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245300 q = 1) (hb : d245630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245300, d245630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245300, d245630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245301 q = 1) (hb : d245631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245301, d245631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245301, d245631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61380 (p : Pattern) (ha : d245307 p = 1) (hb : d245637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d245188 q = 1) (hb : d245466 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245188, d245466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61349 q ha hb
    | true =>
      simp only [d245188, d245466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61355 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245215 q = 1) (hb : d245506 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245215, d245506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245215, d245506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61361 q ha hb
  have h3 (q : Pattern) (ha : d245216 q = 1) (hb : d245507 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245216, d245507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245216, d245507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245243 q = 1) (hb : d245547 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245243, d245547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245243, d245547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61367 q ha hb
  have h5 (q : Pattern) (ha : d245244 q = 1) (hb : d245548 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245244, d245548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245244, d245548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245245 q = 1) (hb : d245549 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245245, d245549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245245, d245549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245272 q = 1) (hb : d245589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245272, d245589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245272, d245589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61373 q ha hb
  have h8 (q : Pattern) (ha : d245273 q = 1) (hb : d245590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245273, d245590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245273, d245590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245274 q = 1) (hb : d245591 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245274, d245591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245274, d245591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245275 q = 1) (hb : d245592 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245275, d245592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245275, d245592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245302 q = 1) (hb : d245632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245302, d245632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245302, d245632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61379 q ha hb
  have h12 (q : Pattern) (ha : d245303 q = 1) (hb : d245633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245303, d245633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245303, d245633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245304 q = 1) (hb : d245634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245304, d245634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245304, d245634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245305 q = 1) (hb : d245635 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245305, d245635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245305, d245635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245306 q = 1) (hb : d245636 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245306, d245636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245306, d245636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245307 q = 1) (hb : d245637 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245307, d245637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245307, d245637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro61381 (p : Pattern) (ha : d245313 p = 1) (hb : d245643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245308 q = 1) (hb : d245638 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245308, d245638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61380 q ha hb
    | true =>
      simp only [d245308, d245638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245309 q = 1) (hb : d245639 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245309, d245639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245309, d245639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245310 q = 1) (hb : d245640 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245310, d245640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245310, d245640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245311 q = 1) (hb : d245641 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245311, d245641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245311, d245641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245312 q = 1) (hb : d245642 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245312, d245642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245312, d245642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245313 q = 1) (hb : d245643 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245313, d245643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245313, d245643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61382 (p : Pattern) (ha : d245319 p = 1) (hb : d245649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245314 q = 1) (hb : d245644 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245314, d245644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61381 q ha hb
    | true =>
      simp only [d245314, d245644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245315 q = 1) (hb : d245645 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245315, d245645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245315, d245645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245316 q = 1) (hb : d245646 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245316, d245646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245316, d245646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245317 q = 1) (hb : d245647 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245317, d245647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245317, d245647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245318 q = 1) (hb : d245648 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245318, d245648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245318, d245648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245319 q = 1) (hb : d245649 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245319, d245649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245319, d245649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61383 (p : Pattern) (ha : d245325 p = 1) (hb : d245655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245320 q = 1) (hb : d245650 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245320, d245650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61382 q ha hb
    | true =>
      simp only [d245320, d245650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245321 q = 1) (hb : d245651 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245321, d245651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245321, d245651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245322 q = 1) (hb : d245652 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245322, d245652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245322, d245652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245323 q = 1) (hb : d245653 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245323, d245653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245323, d245653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245324 q = 1) (hb : d245654 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245324, d245654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245324, d245654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245325 q = 1) (hb : d245655 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245325, d245655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245325, d245655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61384 (p : Pattern) (ha : d245331 p = 1) (hb : d245661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245326 q = 1) (hb : d245656 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245326, d245656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61383 q ha hb
    | true =>
      simp only [d245326, d245656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245327 q = 1) (hb : d245657 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245327, d245657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245327, d245657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245328 q = 1) (hb : d245658 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245328, d245658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245328, d245658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245329 q = 1) (hb : d245659 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245329, d245659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245329, d245659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245330 q = 1) (hb : d245660 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245330, d245660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245330, d245660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245331 q = 1) (hb : d245661 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245331, d245661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245331, d245661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61385 (p : Pattern) (ha : d245337 p = 1) (hb : d245667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245332 q = 1) (hb : d245662 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245332, d245662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61384 q ha hb
    | true =>
      simp only [d245332, d245662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245333 q = 1) (hb : d245663 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245333, d245663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245333, d245663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245334 q = 1) (hb : d245664 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245334, d245664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245334, d245664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245335 q = 1) (hb : d245665 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245335, d245665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245335, d245665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245336 q = 1) (hb : d245666 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245336, d245666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245336, d245666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245337 q = 1) (hb : d245667 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245337, d245667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245337, d245667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61386 (p : Pattern) (ha : d245343 p = 1) (hb : d245673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245338 q = 1) (hb : d245668 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245338, d245668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61385 q ha hb
    | true =>
      simp only [d245338, d245668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245339 q = 1) (hb : d245669 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245339, d245669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245339, d245669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245340 q = 1) (hb : d245670 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245340, d245670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245340, d245670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245341 q = 1) (hb : d245671 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245341, d245671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245341, d245671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245342 q = 1) (hb : d245672 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245342, d245672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245342, d245672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245343 q = 1) (hb : d245673 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245343, d245673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245343, d245673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61387 (p : Pattern) (ha : d245349 p = 1) (hb : d245679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245344 q = 1) (hb : d245674 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245344, d245674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61386 q ha hb
    | true =>
      simp only [d245344, d245674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245345 q = 1) (hb : d245675 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245345, d245675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245345, d245675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245346 q = 1) (hb : d245676 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245346, d245676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245346, d245676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245347 q = 1) (hb : d245677 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245347, d245677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245347, d245677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245348 q = 1) (hb : d245678 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245348, d245678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245348, d245678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245349 q = 1) (hb : d245679 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245349, d245679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245349, d245679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61388 (p : Pattern) (ha : d25104 p = 1) (hb : d198467 p = 1) : d25690 p = 1 := by
  have h0 (q : Pattern) (ha : d25103 q = 1) (hb : d152852 q = 1) : d25103 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25104 q = 1) (hb : d198467 q = 1) : d25690 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25104, d198467, d25690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61389 (p : Pattern) (ha : d25110 p = 1) (hb : d198467 p = 1) : d200251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
    | true =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25109 q = 1) (hb : d198467 q = 1) : d200250 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d200250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25110 q = 1) (hb : d198467 q = 1) : d200251 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25110, d200251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61390 (p : Pattern) (ha : d25116 p = 1) (hb : d198467 p = 1) : d200257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
    | true =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25114 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25114, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d198467 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25115 q = 1) (hb : d198467 q = 1) : d200256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25115, d200256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25116 q = 1) (hb : d198467 q = 1) : d200257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25116, d200257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro61391 (p : Pattern) (ha : d25122 p = 1) (hb : d198467 p = 1) : d200263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25122 q = 1) (hb : d198467 q = 1) : d200263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d200263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61392 (p : Pattern) (ha : d198467 p = 1) (hb : d201977 p = 1) : d200269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25123 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
    | true =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d201973 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d201973, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d201974 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d201975 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d201975, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d201976 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d201976, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d201977 q = 1) : d200269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201977, d200269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61393 (p : Pattern) (ha : d25129 p = 1) (hb : d198467 p = 1) : d200270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d198467 q = 1) : d200262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d200262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25129 q = 1) (hb : d198467 q = 1) : d200270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25129, d200270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61394 (p : Pattern) (ha : d198467 p = 1) (hb : d201982 p = 1) : d200276 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d198467 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d198467 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25123 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
    | true =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d201973 q = 1) : d200265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d201973, d200265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d198467 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d201974 q = 1) : d200266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d200266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d201975 q = 1) : d200267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d201975, d200267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d201976 q = 1) : d200268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201976, d200268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d198467 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d198467 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25130 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
    | true =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d201978 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d201978, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d201979 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201979, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d198467 q = 1) (hb : d201980 q = 1) : d200274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d201980, d200274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198467 q = 1) (hb : d201981 q = 1) : d200275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d201981, d200275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d198467 q = 1) (hb : d201982 q = 1) : d200276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201982, d200276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61395 (p : Pattern) (ha : d198467 p = 1) (hb : d201989 p = 1) : d200283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
    | true =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d201978 q = 1) : d200272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d201978, d200272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d198467 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d201979 q = 1) : d200273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201979, d200273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d201987 q = 1) : d200281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201987, d200281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d201988 q = 1) : d200282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201988, d200282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d201989 q = 1) : d200283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201989, d200283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61396 (p : Pattern) (ha : d25153 p = 1) (hb : d198467 p = 1) : d200290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
    | true =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25152 q = 1) (hb : d198467 q = 1) : d200289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d200289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25153 q = 1) (hb : d198467 q = 1) : d200290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25153, d200290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61397 (p : Pattern) (ha : d25159 p = 1) (hb : d198467 p = 1) : d200296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
    | true =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25157 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25157, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d198467 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25158 q = 1) (hb : d198467 q = 1) : d200295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25158, d200295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25159 q = 1) (hb : d198467 q = 1) : d200296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25159, d200296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro61398 (p : Pattern) (ha : d25165 p = 1) (hb : d198467 p = 1) : d200302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61397 q ha hb
    | true =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d198467 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25162 q = 1) (hb : d198467 q = 1) : d200299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d200299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25163 q = 1) (hb : d198467 q = 1) : d200300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25163, d200300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25164 q = 1) (hb : d198467 q = 1) : d200301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25164, d200301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25165 q = 1) (hb : d198467 q = 1) : d200302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25165, d200302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61399 (p : Pattern) (ha : d198467 p = 1) (hb : d201999 p = 1) : d200308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61398 q ha hb
    | true =>
      simp only [d25166, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d201995 q = 1) : d200304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d201995, d200304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d198467 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d201996 q = 1) : d200305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201996, d200305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d201997 q = 1) : d200306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201997, d200306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d201998 q = 1) : d200307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201998, d200307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d201999 q = 1) : d200308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201999, d200308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61400 (p : Pattern) (ha : d198467 p = 1) (hb : d202005 p = 1) : d200314 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d198467 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d201983 q = 1) : d200277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61392 q ha hb
    | true =>
      simp only [d201983, d200277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61394 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d198467 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d201984 q = 1) : d200278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201984, d200278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d201985 q = 1) : d200279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201985, d200279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d201986 q = 1) : d200280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201986, d200280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d201990 q = 1) : d200284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d201990, d200284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61395 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d201991 q = 1) : d200285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201991, d200285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d201992 q = 1) : d200286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201992, d200286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d201993 q = 1) : d200287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201993, d200287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d201994 q = 1) : d200288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201994, d200288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d202000 q = 1) : d200309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202000, d200309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61399 q ha hb
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d202001 q = 1) : d200310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202001, d200310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202002 q = 1) : d200311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202002, d200311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202003 q = 1) : d200312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202003, d200312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d202004 q = 1) : d200313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202004, d200313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198467 q = 1) (hb : d202005 q = 1) : d200314 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202005, d200314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro61401 (p : Pattern) (ha : d25187 p = 1) (hb : d198467 p = 1) : d200324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
    | true =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25187 q = 1) (hb : d198467 q = 1) : d200324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61402 (p : Pattern) (ha : d25194 p = 1) (hb : d198467 p = 1) : d200331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
    | true =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25130 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
    | true =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25190 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25191 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25191, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25192 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25193 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25194 q = 1) (hb : d198467 q = 1) : d200331 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25194, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro61403 (p : Pattern) (ha : d25296 p = 1) (hb : d198467 p = 1) : d200404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d198467 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d198467 q = 1) : d200264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
    | true =>
      simp only [d25123, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d198467 q = 1) : d200320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d198467 q = 1) : d200321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d198467 q = 1) : d200322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d198467 q = 1) : d200323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d198467 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25296 q = 1) (hb : d198467 q = 1) : d200404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25296, d200404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61404 (p : Pattern) (ha : d25199 p = 1) (hb : d198467 p = 1) : d200336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25199 q = 1) (hb : d198467 q = 1) : d200336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d200336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61405 (p : Pattern) (ha : d25206 p = 1) (hb : d198467 p = 1) : d200343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25206 q = 1) (hb : d198467 q = 1) : d200343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d200343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro61406 (p : Pattern) (ha : d25213 p = 1) (hb : d198467 p = 1) : d200347 p = 1 := by
  have h0 (q : Pattern) (ha : d25212 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25213 q = 1) (hb : d198467 q = 1) : d200347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25213, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61407 (p : Pattern) (ha : d25221 p = 1) (hb : d198467 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d25220 q = 1) (hb : d152852 q = 1) : d25220 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d23 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25221 q = 1) (hb : d198467 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25221, d198467, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61408 (p : Pattern) (ha : d25227 p = 1) (hb : d198467 p = 1) : d200359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
    | true =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
    | true =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d198467 q = 1) : d25693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25224 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25225 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25226 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25226, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25227 q = 1) (hb : d198467 q = 1) : d200359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d200359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro61409 (p : Pattern) (ha : d25233 p = 1) (hb : d198467 p = 1) : d200365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61408 q ha hb
    | true =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
    | true =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d198467 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25114 q = 1) (hb : d198467 q = 1) : d200255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25114, d200255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25232 q = 1) (hb : d198467 q = 1) : d200364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25232, d200364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25233 q = 1) (hb : d198467 q = 1) : d200365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25233, d200365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro61410 (p : Pattern) (ha : d25239 p = 1) (hb : d198467 p = 1) : d200371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61409 q ha hb
    | true =>
      simp only [d25234, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d198467 q = 1) : d200371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d200371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61411 (p : Pattern) (ha : d25267 p = 1) (hb : d198467 p = 1) : d200377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d198467 q = 1) : d200377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d200377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61412 (p : Pattern) (ha : d198467 p = 1) (hb : d202015 p = 1) : d200383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61404 q ha hb
    | true =>
      simp only [d25200, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61405 q ha hb
    | true =>
      simp only [d25207, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61410 q ha hb
    | true =>
      simp only [d25240, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d202011 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202011, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61411 q ha hb
    | true =>
      simp only [d25268, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202012 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202013 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202013, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d202014 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202014, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198467 q = 1) (hb : d202015 q = 1) : d200383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202015, d200383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro61413 (p : Pattern) (ha : d25274 p = 1) (hb : d198467 p = 1) : d200384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d198467 q = 1) : d200261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d200261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d198467 q = 1) : d200335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d200335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25274 q = 1) (hb : d198467 q = 1) : d200384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25274, d200384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61414 (p : Pattern) (ha : d25279 p = 1) (hb : d198467 p = 1) : d200389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d198467 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d198467 q = 1) : d200260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d200260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d198467 q = 1) : d200341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d200341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d198467 q = 1) : d200342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d200342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25279 q = 1) (hb : d198467 q = 1) : d200389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25279, d200389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61415 (p : Pattern) (ha : d25283 p = 1) (hb : d198467 p = 1) : d200393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d198467 q = 1) : d200366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61409 q ha hb
    | true =>
      simp only [d25234, d200366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d198467 q = 1) : d200367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d200367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d198467 q = 1) : d200368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d200368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d198467 q = 1) : d200369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d200369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d198467 q = 1) : d200370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d200370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d198467 q = 1) : d200393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d200393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61416 (p : Pattern) (ha : d25288 p = 1) (hb : d198467 p = 1) : d200396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d198467 q = 1) : d200258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61390 q ha hb
    | true =>
      simp only [d25117, d200258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d198467 q = 1) : d200259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d200259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d198467 q = 1) : d200374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d200374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d198467 q = 1) : d200375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d200375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d198467 q = 1) : d200376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d200376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d198467 q = 1) : d200396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d200396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61417 (p : Pattern) (ha : d198467 p = 1) (hb : d202020 p = 1) : d200402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d198467 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d198467 q = 1) : d200337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61404 q ha hb
    | true =>
      simp only [d25200, d200337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d198467 q = 1) : d200338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d200338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d198467 q = 1) : d200339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d200339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d198467 q = 1) : d200340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d200340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d198467 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d198467 q = 1) : d200344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61405 q ha hb
    | true =>
      simp only [d25207, d200344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d198467 q = 1) : d200345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d200345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d198467 q = 1) : d200346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d200346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d198467 q = 1) : d200372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61410 q ha hb
    | true =>
      simp only [d25240, d200372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61391 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d202011 q = 1) : d200373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202011, d200373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d198467 q = 1) : d200378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61411 q ha hb
    | true =>
      simp only [d25268, d200378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d198467 q = 1) : d200379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d200379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202012 q = 1) : d200380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d200380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202013 q = 1) : d200381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202013, d200381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d202014 q = 1) : d200382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202014, d200382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d198467 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25275 q = 1) (hb : d198467 q = 1) : d200385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61413 q ha hb
    | true =>
      simp only [d25275, d200385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25276 q = 1) (hb : d198467 q = 1) : d200386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d200386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d25277 q = 1) (hb : d198467 q = 1) : d200387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25277, d200387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d25278 q = 1) (hb : d198467 q = 1) : d200388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d200388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d198467 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d25280 q = 1) (hb : d198467 q = 1) : d200390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61414 q ha hb
    | true =>
      simp only [d25280, d200390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d25281 q = 1) (hb : d198467 q = 1) : d200391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d200391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25282 q = 1) (hb : d198467 q = 1) : d200392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25282, d200392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25284 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61415 q ha hb
    | true =>
      simp only [d25284, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
  have h27 (q : Pattern) (ha : d198467 q = 1) (hb : d202016 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d202016, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d25289 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61416 q ha hb
    | true =>
      simp only [d25289, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d25290 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d25290, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d198467 q = 1) (hb : d202017 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d202017, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d198467 q = 1) (hb : d202018 q = 1) : d200400 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d202018, d200400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d198467 q = 1) (hb : d202019 q = 1) : d200401 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202019, d200401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d198467 q = 1) (hb : d202020 q = 1) : d200402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202020, d200402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro61418 (p : Pattern) (ha : d198467 p = 1) (hb : d202027 p = 1) : d200411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d198467 q = 1) : d200394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61415 q ha hb
    | true =>
      simp only [d25284, d200394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202016 q = 1) : d200395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202016, d200395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d198467 q = 1) : d200397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61416 q ha hb
    | true =>
      simp only [d25289, d200397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d198467 q = 1) : d200398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d200398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202017 q = 1) : d200399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d200399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202025 q = 1) : d200409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202025, d200409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d202026 q = 1) : d200410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202026, d200410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202027 q = 1) : d200411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202027, d200411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61419 (p : Pattern) (ha : d25319 p = 1) (hb : d198467 p = 1) : d200427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
    | true =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d198467 q = 1) : d25948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d198467 q = 1) : d25691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61388 q ha hb
    | true =>
      simp only [d25105, d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d198467 q = 1) : d25949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d198467 q = 1) : d25692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d198467 q = 1) : d25950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25314 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
  have h15 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25315 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25316 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25317 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d25318 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25318, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d25319 q = 1) (hb : d198467 q = 1) : d200427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d200427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro61420 (p : Pattern) (ha : d25325 p = 1) (hb : d198467 p = 1) : d200433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61419 q ha hb
    | true =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25154 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
    | true =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25155 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25156 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25323 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d198467 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25157 q = 1) (hb : d198467 q = 1) : d200294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25157, d200294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25324 q = 1) (hb : d198467 q = 1) : d200432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25324, d200432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25325 q = 1) (hb : d198467 q = 1) : d200433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25325, d200433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro61421 (p : Pattern) (ha : d25331 p = 1) (hb : d198467 p = 1) : d200439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d198467 q = 1) : d200434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61420 q ha hb
    | true =>
      simp only [d25326, d200434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d198467 q = 1) : d200435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d200435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61397 q ha hb
    | true =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d198467 q = 1) : d200436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d200436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d198467 q = 1) : d200437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d200437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d198467 q = 1) : d200438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d200438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d198467 q = 1) : d200439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d200439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61422 (p : Pattern) (ha : d25356 p = 1) (hb : d198467 p = 1) : d200445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d198467 q = 1) : d200297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61397 q ha hb
    | true =>
      simp only [d25160, d200297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d198467 q = 1) : d200298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d200298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d198467 q = 1) : d200442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d200442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d198467 q = 1) : d200443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d200443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d198467 q = 1) : d200444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d200444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d198467 q = 1) : d200445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d200445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61423 (p : Pattern) (ha : d198467 p = 1) (hb : d202037 p = 1) : d200451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d198467 q = 1) : d200440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61421 q ha hb
    | true =>
      simp only [d25332, d200440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61398 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202033 q = 1) : d200441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202033, d200441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d198467 q = 1) : d200446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61422 q ha hb
    | true =>
      simp only [d25357, d200446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d198467 q = 1) : d200447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d200447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202034 q = 1) : d200448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d200448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202035 q = 1) : d200449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202035, d200449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d202036 q = 1) : d200450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202036, d200450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202037 q = 1) : d200451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202037, d200451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61424 (p : Pattern) (ha : d198467 p = 1) (hb : d202043 p = 1) : d200457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d198467 q = 1) : d200325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d200325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61401 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d198467 q = 1) : d200326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d200326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61401 q ha hb
    | true =>
      simp only [d25195, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61402 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d198467 q = 1) : d200334 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d200334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202021 q = 1) : d200403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61412 q ha hb
    | true =>
      simp only [d202021, d200403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61417 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d198467 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25297 q = 1) (hb : d198467 q = 1) : d200405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61403 q ha hb
    | true =>
      simp only [d25297, d200405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d202022 q = 1) : d200406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d200406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d202023 q = 1) : d200407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202023, d200407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d202024 q = 1) : d200408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202024, d200408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d202028 q = 1) : d200412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202028, d200412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61418 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d198467 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202029 q = 1) : d200413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202029, d200413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202030 q = 1) : d200414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202030, d200414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d202031 q = 1) : d200415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202031, d200415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d198467 q = 1) (hb : d202032 q = 1) : d200416 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202032, d200416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198467 q = 1) (hb : d202038 q = 1) : d200452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202038, d200452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61423 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d198467 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d198467 q = 1) (hb : d202039 q = 1) : d200453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202039, d200453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d198467 q = 1) (hb : d202040 q = 1) : d200454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202040, d200454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d198467 q = 1) (hb : d202041 q = 1) : d200455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202041, d200455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d198467 q = 1) (hb : d202042 q = 1) : d200456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202042, d200456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d198467 q = 1) (hb : d202043 q = 1) : d200457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202043, d200457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro61425 (p : Pattern) (ha : d198467 p = 1) (hb : d202049 p = 1) : d200463 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d198467 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202006 q = 1) : d200315 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202006, d200315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61400 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d202007 q = 1) : d200316 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202007, d200316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d202008 q = 1) : d200317 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202008, d200317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202009 q = 1) : d200318 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202009, d200318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202010 q = 1) : d200319 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202010, d200319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d202044 q = 1) : d200458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202044, d200458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61424 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202045 q = 1) : d200459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202045, d200459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d202046 q = 1) : d200460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202046, d200460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d202047 q = 1) : d200461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202047, d200461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d202048 q = 1) : d200462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202048, d200462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d202049 q = 1) : d200463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202049, d200463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro61426 (p : Pattern) (ha : d25377 p = 1) (hb : d198467 p = 1) : d200466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61408 q ha hb
    | true =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
    | true =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25375 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25375, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25376 q = 1) (hb : d198467 q = 1) : d200465 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25376, d200465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25377 q = 1) (hb : d198467 q = 1) : d200466 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25377, d200466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro61427 (p : Pattern) (ha : d25381 p = 1) (hb : d198467 p = 1) : d200470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
    | true =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25375 q = 1) (hb : d198467 q = 1) : d200464 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25375, d200464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25380 q = 1) (hb : d198467 q = 1) : d200469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25380, d200469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25381 q = 1) (hb : d198467 q = 1) : d200470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25381, d200470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61428 (p : Pattern) (ha : d25387 p = 1) (hb : d198467 p = 1) : d200476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d198467 q = 1) : d200476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d200476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61429 (p : Pattern) (ha : d25391 p = 1) (hb : d198467 p = 1) : d200480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d198467 q = 1) : d200480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d200480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61430 (p : Pattern) (ha : d25397 p = 1) (hb : d198467 p = 1) : d200486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61428 q ha hb
    | true =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61429 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d198467 q = 1) : d200486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61431 (p : Pattern) (ha : d25400 p = 1) (hb : d198467 p = 1) : d200489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d198467 q = 1) : d200475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d200475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d198467 q = 1) : d200489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d200489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61432 (p : Pattern) (ha : d25401 p = 1) (hb : d198467 p = 1) : d200490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d198467 q = 1) : d200479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d200479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d198467 q = 1) : d200490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d200490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61433 (p : Pattern) (ha : d25407 p = 1) (hb : d198467 p = 1) : d200496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61428 q ha hb
    | true =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61429 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61431 q ha hb
    | true =>
      simp only [d25402, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61432 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d198467 q = 1) : d200496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61434 (p : Pattern) (ha : d25556 p = 1) (hb : d198467 p = 1) : d200585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d198467 q = 1) : d200481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61428 q ha hb
    | true =>
      simp only [d25392, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61429 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d198467 q = 1) : d200482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d198467 q = 1) : d200483 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d198467 q = 1) : d200484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d198467 q = 1) : d200485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61429 q ha hb
    | true =>
      simp only [d25551, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d198467 q = 1) : d200585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d200585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61435 (p : Pattern) (ha : d25562 p = 1) (hb : d198467 p = 1) : d200591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d198467 q = 1) : d200580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61429 q ha hb
    | true =>
      simp only [d25551, d200580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d198467 q = 1) : d200581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d200581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d198467 q = 1) : d200582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d200582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d198467 q = 1) : d200583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d200583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d198467 q = 1) : d200584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d200584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61432 q ha hb
    | true =>
      simp only [d25557, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d198467 q = 1) : d200591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d200591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61436 (p : Pattern) (ha : d25571 p = 1) (hb : d198467 p = 1) : d200600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d198467 q = 1) : d200586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61432 q ha hb
    | true =>
      simp only [d25557, d200586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d198467 q = 1) : d200587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d200587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d198467 q = 1) : d200588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d200588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d198467 q = 1) : d200589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d200589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d198467 q = 1) : d200590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d200590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d198467 q = 1) : d200600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d200600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61437 (p : Pattern) (ha : d25614 p = 1) (hb : d198467 p = 1) : d200639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
    | true =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25604 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25604, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25613 q = 1) (hb : d198467 q = 1) : d200638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25613, d200638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25614 q = 1) (hb : d198467 q = 1) : d200639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25614, d200639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61438 (p : Pattern) (ha : d25670 p = 1) (hb : d198467 p = 1) : d200662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61437 q ha hb
    | true =>
      simp only [d25615, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d198467 q = 1) : d200659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d200659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d198467 q = 1) : d200660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d200660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d198467 q = 1) : d200661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d200661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d198467 q = 1) : d200662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d200662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61439 (p : Pattern) (ha : d25676 p = 1) (hb : d198467 p = 1) : d200668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d198467 q = 1) : d200663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61438 q ha hb
    | true =>
      simp only [d25671, d200663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d198467 q = 1) : d200664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d200664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d198467 q = 1) : d200665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d200665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d198467 q = 1) : d200666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d200666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d198467 q = 1) : d200667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d200667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d198467 q = 1) : d200668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d200668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61440 (p : Pattern) (ha : d25412 p = 1) (hb : d198467 p = 1) : d200501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d198467 q = 1) : d200501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d200501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61441 (p : Pattern) (ha : d25414 p = 1) (hb : d198467 p = 1) : d200503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d198467 q = 1) : d200503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d200503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61442 (p : Pattern) (ha : d25421 p = 1) (hb : d198467 p = 1) : d200510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d198467 q = 1) : d200510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d200510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61443 (p : Pattern) (ha : d25424 p = 1) (hb : d198467 p = 1) : d200513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d198467 q = 1) : d200513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d200513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61444 (p : Pattern) (ha : d25438 p = 1) (hb : d198467 p = 1) : d200517 p = 1 := by
  have h0 (q : Pattern) (ha : d25431 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25438 q = 1) (hb : d198467 q = 1) : d200517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25438, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61445 (p : Pattern) (ha : d25443 p = 1) (hb : d198467 p = 1) : d200347 p = 1 := by
  have h0 (q : Pattern) (ha : d25212 q = 1) (hb : d152852 q = 1) : d25212 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25220 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25443 q = 1) (hb : d198467 q = 1) : d200347 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25443, d198467, d200347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61446 (p : Pattern) (ha : d25451 p = 1) (hb : d198467 p = 1) : d200523 p = 1 := by
  have h0 (q : Pattern) (ha : d25450 q = 1) (hb : d152852 q = 1) : d25450 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25220 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25451 q = 1) (hb : d198467 q = 1) : d200523 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25451, d198467, d200523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61447 (p : Pattern) (ha : d25457 p = 1) (hb : d198467 p = 1) : d200529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61444 q ha hb
    | true =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61445 q ha hb
    | true =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
    | true =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25224 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25225 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25456 q = 1) (hb : d198467 q = 1) : d200528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25456, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25456, d200528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25457 q = 1) (hb : d198467 q = 1) : d200529 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d200529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61448 (p : Pattern) (ha : d25461 p = 1) (hb : d198467 p = 1) : d200533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25224 q = 1) (hb : d198467 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25225 q = 1) (hb : d198467 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25225, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d198467 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25226 q = 1) (hb : d198467 q = 1) : d200358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25226, d200358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d198467 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25461 q = 1) (hb : d198467 q = 1) : d200533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25461, d200533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61449 (p : Pattern) (ha : d25467 p = 1) (hb : d198467 p = 1) : d200539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d198467 q = 1) : d200530 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61447 q ha hb
    | true =>
      simp only [d25458, d200530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61408 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d198467 q = 1) : d200531 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d200531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d198467 q = 1) : d200532 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d200532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25462 q = 1) (hb : d198467 q = 1) : d200534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61408 q ha hb
    | true =>
      simp only [d25462, d200534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61448 q ha hb
  have h5 (q : Pattern) (ha : d25463 q = 1) (hb : d198467 q = 1) : d200535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d200535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25464 q = 1) (hb : d198467 q = 1) : d200536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d200536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25465 q = 1) (hb : d198467 q = 1) : d200537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d200537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25228 q = 1) (hb : d198467 q = 1) : d200360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61408 q ha hb
    | true =>
      simp only [d25228, d200360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
  have h9 (q : Pattern) (ha : d25229 q = 1) (hb : d198467 q = 1) : d200361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d200361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25230 q = 1) (hb : d198467 q = 1) : d200362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d200362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d198467 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25111 q = 1) (hb : d198467 q = 1) : d200252 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61389 q ha hb
    | true =>
      simp only [d25111, d200252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25112 q = 1) (hb : d198467 q = 1) : d200253 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d200253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25113 q = 1) (hb : d198467 q = 1) : d200254 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d200254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25231 q = 1) (hb : d198467 q = 1) : d200363 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25231, d200363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25466 q = 1) (hb : d198467 q = 1) : d200538 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25466, d200538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25467 q = 1) (hb : d198467 q = 1) : d200539 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25467, d200539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro61450 (p : Pattern) (ha : d25473 p = 1) (hb : d198467 p = 1) : d200545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61449 q ha hb
    | true =>
      simp only [d25468, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d198467 q = 1) : d200545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d200545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61451 (p : Pattern) (ha : d25519 p = 1) (hb : d198467 p = 1) : d200551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d198467 q = 1) : d200551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d200551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61452 (p : Pattern) (ha : d198467 p = 1) (hb : d202054 p = 1) : d200557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61440 q ha hb
    | true =>
      simp only [d25415, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61441 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61442 q ha hb
    | true =>
      simp only [d25425, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61443 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61450 q ha hb
    | true =>
      simp only [d25474, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61428 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d202050 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202050, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61451 q ha hb
    | true =>
      simp only [d25520, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d202051 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d202052 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202052, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202053 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202053, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202054 q = 1) : d200557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202054, d200557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro61453 (p : Pattern) (ha : d25526 p = 1) (hb : d198467 p = 1) : d200558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d198467 q = 1) : d200474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d200474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d198467 q = 1) : d200500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d200500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d198467 q = 1) : d200558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d200558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61454 (p : Pattern) (ha : d25527 p = 1) (hb : d198467 p = 1) : d200559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d198467 q = 1) : d200478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d200478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d198467 q = 1) : d200502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d200502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d198467 q = 1) : d200559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d200559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61455 (p : Pattern) (ha : d25532 p = 1) (hb : d198467 p = 1) : d200564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d198467 q = 1) : d200473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d200473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d198467 q = 1) : d200508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d200508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d198467 q = 1) : d200509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d200509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d198467 q = 1) : d200564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d200564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61456 (p : Pattern) (ha : d25533 p = 1) (hb : d198467 p = 1) : d200565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d198467 q = 1) : d200471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61427 q ha hb
    | true =>
      simp only [d25382, d200471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d198467 q = 1) : d200472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d200472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d198467 q = 1) : d200477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d200477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d198467 q = 1) : d200511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d200511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d198467 q = 1) : d200512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d200512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d198467 q = 1) : d200565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d200565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61457 (p : Pattern) (ha : d25537 p = 1) (hb : d198467 p = 1) : d200569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d198467 q = 1) : d200540 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61449 q ha hb
    | true =>
      simp only [d25468, d200540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d198467 q = 1) : d200541 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d200541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d198467 q = 1) : d200542 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d200542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d198467 q = 1) : d200543 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d200543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d198467 q = 1) : d200544 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d200544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d198467 q = 1) : d200569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d200569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61458 (p : Pattern) (ha : d25543 p = 1) (hb : d198467 p = 1) : d200572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d198467 q = 1) : d200467 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61426 q ha hb
    | true =>
      simp only [d25378, d200467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d198467 q = 1) : d200468 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d200468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d198467 q = 1) : d200548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d200548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d198467 q = 1) : d200549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d200549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d198467 q = 1) : d200550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d200550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d198467 q = 1) : d200572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d200572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61459 (p : Pattern) (ha : d198467 p = 1) (hb : d202059 p = 1) : d200578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d198467 q = 1) : d200504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61440 q ha hb
    | true =>
      simp only [d25415, d200504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61441 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d198467 q = 1) : d200505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d200505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d198467 q = 1) : d200506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d200506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d198467 q = 1) : d200507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d200507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d198467 q = 1) : d200514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61442 q ha hb
    | true =>
      simp only [d25425, d200514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61443 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d198467 q = 1) : d200515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d200515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d198467 q = 1) : d200516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d200516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d198467 q = 1) : d200546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61450 q ha hb
    | true =>
      simp only [d25474, d200546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61428 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d202050 q = 1) : d200547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202050, d200547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d198467 q = 1) : d200552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61451 q ha hb
    | true =>
      simp only [d25520, d200552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d198467 q = 1) : d200553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d200553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d202051 q = 1) : d200554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d200554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d202052 q = 1) : d200555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202052, d200555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202053 q = 1) : d200556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202053, d200556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d198467 q = 1) : d200560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61453 q ha hb
    | true =>
      simp only [d25528, d200560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61454 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d198467 q = 1) : d200561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d200561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d198467 q = 1) : d200562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d200562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d198467 q = 1) : d200563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d200563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d198467 q = 1) : d200566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61455 q ha hb
    | true =>
      simp only [d25534, d200566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61456 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d198467 q = 1) : d200567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d200567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d198467 q = 1) : d200568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d200568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61457 q ha hb
    | true =>
      simp only [d25538, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61431 q ha hb
  have h23 (q : Pattern) (ha : d198467 q = 1) (hb : d202055 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202055, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61458 q ha hb
    | true =>
      simp only [d25544, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d198467 q = 1) (hb : d202056 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d198467 q = 1) (hb : d202057 q = 1) : d200576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202057, d200576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d198467 q = 1) (hb : d202058 q = 1) : d200577 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202058, d200577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d198467 q = 1) (hb : d202059 q = 1) : d200578 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d200578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro61460 (p : Pattern) (ha : d198467 p = 1) (hb : d202066 p = 1) : d200598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d198467 q = 1) : d200570 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61457 q ha hb
    | true =>
      simp only [d25538, d200570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61431 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202055 q = 1) : d200571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202055, d200571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d198467 q = 1) : d200573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61458 q ha hb
    | true =>
      simp only [d25544, d200573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d198467 q = 1) : d200574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d200574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202056 q = 1) : d200575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d200575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202064 q = 1) : d200596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202064, d200596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d202065 q = 1) : d200597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202065, d200597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202066 q = 1) : d200598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202066, d200598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61461 (p : Pattern) (ha : d25591 p = 1) (hb : d198467 p = 1) : d200616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d198467 q = 1) : d200606 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d200606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61444 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61444 q ha hb
    | true =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d198467 q = 1) : d200607 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d200607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d198467 q = 1) : d200608 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d200608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d198467 q = 1) : d200609 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d200609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61445 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61445 q ha hb
    | true =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d198467 q = 1) : d200610 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d200610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25586 q = 1) (hb : d198467 q = 1) : d200611 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d200611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
  have h15 (q : Pattern) (ha : d25452 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
    | true =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25587 q = 1) (hb : d198467 q = 1) : d200612 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25587, d200612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25453 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25588 q = 1) (hb : d198467 q = 1) : d200613 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25588, d200613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25589 q = 1) (hb : d198467 q = 1) : d200614 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25589, d200614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25314 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
  have h21 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25315 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25316 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25317 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25590 q = 1) (hb : d198467 q = 1) : d200615 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25590, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25590, d200615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25591 q = 1) (hb : d198467 q = 1) : d200616 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d200616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro61462 (p : Pattern) (ha : d25595 p = 1) (hb : d198467 p = 1) : d200620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25314 q = 1) (hb : d198467 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
  have h2 (q : Pattern) (ha : d25222 q = 1) (hb : d198467 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61407 q ha hb
    | true =>
      simp only [d25222, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25315 q = 1) (hb : d198467 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25315, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25223 q = 1) (hb : d198467 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25223, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25316 q = 1) (hb : d198467 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25316, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25317 q = 1) (hb : d198467 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25317, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d198467 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25318 q = 1) (hb : d198467 q = 1) : d200426 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25318, d200426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d198467 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25595 q = 1) (hb : d198467 q = 1) : d200620 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25595, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25595, d200620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61463 (p : Pattern) (ha : d25601 p = 1) (hb : d198467 p = 1) : d200626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25592 q = 1) (hb : d198467 q = 1) : d200617 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25592, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61461 q ha hb
    | true =>
      simp only [d25592, d200617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61419 q ha hb
  have h2 (q : Pattern) (ha : d25593 q = 1) (hb : d198467 q = 1) : d200618 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25593, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25593, d200618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25594 q = 1) (hb : d198467 q = 1) : d200619 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25594, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25594, d200619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25596 q = 1) (hb : d198467 q = 1) : d200621 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25596, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61419 q ha hb
    | true =>
      simp only [d25596, d200621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61462 q ha hb
  have h5 (q : Pattern) (ha : d25597 q = 1) (hb : d198467 q = 1) : d200622 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25597, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25597, d200622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25598 q = 1) (hb : d198467 q = 1) : d200623 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25598, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25598, d200623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25599 q = 1) (hb : d198467 q = 1) : d200624 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25599, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25599, d200624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25320 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61419 q ha hb
    | true =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
  have h9 (q : Pattern) (ha : d25321 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25322 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25154 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
    | true =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25155 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25156 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25323 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25600 q = 1) (hb : d198467 q = 1) : d200625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25600, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25600, d200625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25601 q = 1) (hb : d198467 q = 1) : d200626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25601, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25601, d200626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro61464 (p : Pattern) (ha : d25606 p = 1) (hb : d198467 p = 1) : d200631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d198467 q = 1) : d200428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61419 q ha hb
    | true =>
      simp only [d25320, d200428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d198467 q = 1) : d200429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d200429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d198467 q = 1) : d200430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d200430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d198467 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25154 q = 1) (hb : d198467 q = 1) : d200291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61396 q ha hb
    | true =>
      simp only [d25154, d200291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25155 q = 1) (hb : d198467 q = 1) : d200292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d200292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25156 q = 1) (hb : d198467 q = 1) : d200293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d200293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25323 q = 1) (hb : d198467 q = 1) : d200431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d200431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25604 q = 1) (hb : d198467 q = 1) : d200629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25604, d200629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25605 q = 1) (hb : d198467 q = 1) : d200630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25605, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25605, d200630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25606 q = 1) (hb : d198467 q = 1) : d200631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25606, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25606, d200631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro61465 (p : Pattern) (ha : d25612 p = 1) (hb : d198467 p = 1) : d200637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25602 q = 1) (hb : d198467 q = 1) : d200627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25602, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61463 q ha hb
    | true =>
      simp only [d25602, d200627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25603 q = 1) (hb : d198467 q = 1) : d200628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25603, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25603, d200628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25607 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61464 q ha hb
    | true =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25608 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25609 q = 1) (hb : d198467 q = 1) : d200634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25609, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25609, d200634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25610 q = 1) (hb : d198467 q = 1) : d200635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25610, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25610, d200635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25611 q = 1) (hb : d198467 q = 1) : d200636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25611, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25611, d200636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25612 q = 1) (hb : d198467 q = 1) : d200637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25612, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25612, d200637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61466 (p : Pattern) (ha : d25620 p = 1) (hb : d198467 p = 1) : d200645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61464 q ha hb
    | true =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25615 q = 1) (hb : d198467 q = 1) : d200640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61437 q ha hb
    | true =>
      simp only [d25615, d200640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25616 q = 1) (hb : d198467 q = 1) : d200641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d200641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25617 q = 1) (hb : d198467 q = 1) : d200642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25617, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25617, d200642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25618 q = 1) (hb : d198467 q = 1) : d200643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25618, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25618, d200643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25619 q = 1) (hb : d198467 q = 1) : d200644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25619, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25619, d200644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25620 q = 1) (hb : d198467 q = 1) : d200645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25620, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25620, d200645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61467 (p : Pattern) (ha : d25659 p = 1) (hb : d198467 p = 1) : d200651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d198467 q = 1) : d200632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61464 q ha hb
    | true =>
      simp only [d25607, d200632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d198467 q = 1) : d200633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d200633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25656 q = 1) (hb : d198467 q = 1) : d200648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25656, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25656, d200648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25657 q = 1) (hb : d198467 q = 1) : d200649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25657, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25657, d200649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25658 q = 1) (hb : d198467 q = 1) : d200650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25658, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25658, d200650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25659 q = 1) (hb : d198467 q = 1) : d200651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25659, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25659, d200651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61468 (p : Pattern) (ha : d198467 p = 1) (hb : d202076 p = 1) : d200657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25621 q = 1) (hb : d198467 q = 1) : d200646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25621, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61465 q ha hb
    | true =>
      simp only [d25621, d200646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61466 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202072 q = 1) : d200647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202072, d200647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25660 q = 1) (hb : d198467 q = 1) : d200652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25660, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61467 q ha hb
    | true =>
      simp only [d25660, d200652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25661 q = 1) (hb : d198467 q = 1) : d200653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25661, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25661, d200653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202073 q = 1) : d200654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202073, d200654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202074 q = 1) : d200655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202074, d200655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d202075 q = 1) : d200656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202075, d200656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202076 q = 1) : d200657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202076, d200657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61469 (p : Pattern) (ha : d198467 p = 1) (hb : d202082 p = 1) : d200674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25398 q = 1) (hb : d198467 q = 1) : d200487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25398, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25398, d200487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61430 q ha hb
  have h2 (q : Pattern) (ha : d25399 q = 1) (hb : d198467 q = 1) : d200488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25399, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25399, d200488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25408 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61430 q ha hb
    | true =>
      simp only [d25408, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61433 q ha hb
  have h4 (q : Pattern) (ha : d25409 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25409, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25410 q = 1) (hb : d198467 q = 1) : d200499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25410, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25410, d200499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202060 q = 1) : d200579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61452 q ha hb
    | true =>
      simp only [d202060, d200579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61459 q ha hb
  have h7 (q : Pattern) (ha : d25563 q = 1) (hb : d198467 q = 1) : d200592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25563, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61434 q ha hb
    | true =>
      simp only [d25563, d200592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61435 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d202061 q = 1) : d200593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202061, d200593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d202062 q = 1) : d200594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202062, d200594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d202063 q = 1) : d200595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202063, d200595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d202067 q = 1) : d200599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202067, d200599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61460 q ha hb
  have h12 (q : Pattern) (ha : d25572 q = 1) (hb : d198467 q = 1) : d200601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25572, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25572, d200601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61436 q ha hb
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d202068 q = 1) : d200602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202068, d200602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d202069 q = 1) : d200603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202069, d200603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d202070 q = 1) : d200604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202070, d200604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d202071 q = 1) : d200605 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202071, d200605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198467 q = 1) (hb : d202077 q = 1) : d200658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202077, d200658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61468 q ha hb
  have h18 (q : Pattern) (ha : d25677 q = 1) (hb : d198467 q = 1) : d200669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25677, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25677, d200669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61439 q ha hb
  have h19 (q : Pattern) (ha : d198467 q = 1) (hb : d202078 q = 1) : d200670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202078, d200670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d198467 q = 1) (hb : d202079 q = 1) : d200671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202079, d200671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d198467 q = 1) (hb : d202080 q = 1) : d200672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202080, d200672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d198467 q = 1) (hb : d202081 q = 1) : d200673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202081, d200673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d198467 q = 1) (hb : d202082 q = 1) : d200674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202082, d200674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro61470 (p : Pattern) (ha : d198467 p = 1) (hb : d202088 p = 1) : d200680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d202083 q = 1) : d200675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202083, d200675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61469 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d202084 q = 1) : d200676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202084, d200676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d202085 q = 1) : d200677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202085, d200677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d202086 q = 1) : d200678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202086, d200678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d202087 q = 1) : d200679 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202087, d200679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d202088 q = 1) : d200680 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202088, d200680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61471 (p : Pattern) (ha : d25696 p = 1) (hb : d198467 p = 1) : d200683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61444 q ha hb
    | true =>
      simp only [d25439, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61445 q ha hb
    | true =>
      simp only [d25444, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d198467 q = 1) : d200522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d200522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
    | true =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25694 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25695 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25695, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25696 q = 1) (hb : d198467 q = 1) : d200683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25696, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25696, d200683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro61472 (p : Pattern) (ha : d25699 p = 1) (hb : d198467 p = 1) : d200684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
    | true =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d198467 q = 1) : d200350 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d200350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d198467 q = 1) : d200351 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d200351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25694 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25697 q = 1) (hb : d198467 q = 1) : d200352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25697, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25697, d200352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25698 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25699 q = 1) (hb : d198467 q = 1) : d200684 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25699, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25699, d200684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61473 (p : Pattern) (ha : d25710 p = 1) (hb : d198467 p = 1) : d200694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25700 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61471 q ha hb
    | true =>
      simp only [d25700, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61472 q ha hb
  have h2 (q : Pattern) (ha : d25701 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25702 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25703 q = 1) (hb : d198467 q = 1) : d25703 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25704 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61472 q ha hb
    | true =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25705 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25706 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25707 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25707, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25708 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25708, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25709 q = 1) (hb : d198467 q = 1) : d200693 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25709, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25709, d200693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25710 q = 1) (hb : d198467 q = 1) : d200694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25710, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25710, d200694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro61474 (p : Pattern) (ha : d25714 p = 1) (hb : d198467 p = 1) : d200698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25703 q = 1) (hb : d198467 q = 1) : d25703 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25704 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61472 q ha hb
    | true =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25705 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25706 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25708 q = 1) (hb : d198467 q = 1) : d200692 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25708, d200692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25713 q = 1) (hb : d198467 q = 1) : d200697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25713, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25713, d200697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25714 q = 1) (hb : d198467 q = 1) : d200698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25714, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25714, d200698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61475 (p : Pattern) (ha : d25720 p = 1) (hb : d198467 p = 1) : d200704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25720 q = 1) (hb : d198467 q = 1) : d200704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25720, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25720, d200704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61476 (p : Pattern) (ha : d25724 p = 1) (hb : d198467 p = 1) : d200708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25724 q = 1) (hb : d198467 q = 1) : d200708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25724, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25724, d200708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61477 (p : Pattern) (ha : d25730 p = 1) (hb : d198467 p = 1) : d200714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61475 q ha hb
    | true =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61476 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25730 q = 1) (hb : d198467 q = 1) : d200714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25730, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25730, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61478 (p : Pattern) (ha : d25733 p = 1) (hb : d198467 p = 1) : d200717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d198467 q = 1) : d200703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d200703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25733 q = 1) (hb : d198467 q = 1) : d200717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25733, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25733, d200717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro61479 (p : Pattern) (ha : d25734 p = 1) (hb : d198467 p = 1) : d200718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d198467 q = 1) : d200707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d200707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25734 q = 1) (hb : d198467 q = 1) : d200718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25734, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25734, d200718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61480 (p : Pattern) (ha : d25740 p = 1) (hb : d198467 p = 1) : d200724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61475 q ha hb
    | true =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61476 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25735 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61478 q ha hb
    | true =>
      simp only [d25735, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61479 q ha hb
  have h7 (q : Pattern) (ha : d25736 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25737 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25737, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25738 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25739 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25740 q = 1) (hb : d198467 q = 1) : d200724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25740, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25740, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61481 (p : Pattern) (ha : d25912 p = 1) (hb : d198467 p = 1) : d200813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d198467 q = 1) : d200709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61475 q ha hb
    | true =>
      simp only [d25725, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61476 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d198467 q = 1) : d200710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d198467 q = 1) : d200711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d198467 q = 1) : d200712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d198467 q = 1) : d200713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25907 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61476 q ha hb
    | true =>
      simp only [d25907, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25908 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25909 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25909, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25910 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25911 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25912 q = 1) (hb : d198467 q = 1) : d200813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25912, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25912, d200813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61482 (p : Pattern) (ha : d25918 p = 1) (hb : d198467 p = 1) : d200819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25907 q = 1) (hb : d198467 q = 1) : d200808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61476 q ha hb
    | true =>
      simp only [d25907, d200808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25908 q = 1) (hb : d198467 q = 1) : d200809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d200809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25909 q = 1) (hb : d198467 q = 1) : d200810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25909, d200810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25910 q = 1) (hb : d198467 q = 1) : d200811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d200811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25911 q = 1) (hb : d198467 q = 1) : d200812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d200812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25913 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61479 q ha hb
    | true =>
      simp only [d25913, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25914 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25915 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25915, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25916 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25917 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25918 q = 1) (hb : d198467 q = 1) : d200819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25918, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25918, d200819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro61483 (p : Pattern) (ha : d25927 p = 1) (hb : d198467 p = 1) : d200828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25913 q = 1) (hb : d198467 q = 1) : d200814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61479 q ha hb
    | true =>
      simp only [d25913, d200814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25914 q = 1) (hb : d198467 q = 1) : d200815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d200815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25915 q = 1) (hb : d198467 q = 1) : d200816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25915, d200816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25916 q = 1) (hb : d198467 q = 1) : d200817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d200817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25917 q = 1) (hb : d198467 q = 1) : d200818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d200818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25927 q = 1) (hb : d198467 q = 1) : d200828 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25927, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25927, d200828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61484 (p : Pattern) (ha : d25964 p = 1) (hb : d198467 p = 1) : d200855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d198467 q = 1) : d200417 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d200417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d198467 q = 1) : d200348 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61406 q ha hb
    | true =>
      simp only [d25214, d200348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d198467 q = 1) : d200418 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d200418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d198467 q = 1) : d200349 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d200349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d198467 q = 1) : d200419 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d200419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d198467 q = 1) : d200420 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d200420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25951 q = 1) (hb : d198467 q = 1) : d25951 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25963 q = 1) (hb : d198467 q = 1) : d200421 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25963, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25963, d200421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25957 q = 1) (hb : d198467 q = 1) : d25957 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25964 q = 1) (hb : d198467 q = 1) : d200855 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25964, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25964, d200855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro61485 (p : Pattern) (ha : d25987 p = 1) (hb : d198467 p = 1) : d200877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25968 q = 1) (hb : d198467 q = 1) : d25968 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25969 q = 1) (hb : d198467 q = 1) : d200859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61484 q ha hb
    | true =>
      simp only [d25969, d200859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25970 q = 1) (hb : d198467 q = 1) : d200860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d200860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25971 q = 1) (hb : d198467 q = 1) : d200861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d200861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25977 q = 1) (hb : d198467 q = 1) : d200867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25977, d200867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25986 q = 1) (hb : d198467 q = 1) : d200876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25986, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25986, d200876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25987 q = 1) (hb : d198467 q = 1) : d200877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25987, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25987, d200877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro61486 (p : Pattern) (ha : d26058 p = 1) (hb : d198467 p = 1) : d200900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25988 q = 1) (hb : d198467 q = 1) : d200878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61485 q ha hb
    | true =>
      simp only [d25988, d200878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25989 q = 1) (hb : d198467 q = 1) : d200879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d200879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26055 q = 1) (hb : d198467 q = 1) : d200897 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26055, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26055, d200897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26056 q = 1) (hb : d198467 q = 1) : d200898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26056, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26056, d200898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26057 q = 1) (hb : d198467 q = 1) : d200899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26057, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26057, d200899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26058 q = 1) (hb : d198467 q = 1) : d200900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26058, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26058, d200900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro61487 (p : Pattern) (ha : d26064 p = 1) (hb : d198467 p = 1) : d200906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26059 q = 1) (hb : d198467 q = 1) : d200901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26059, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61486 q ha hb
    | true =>
      simp only [d26059, d200901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26060 q = 1) (hb : d198467 q = 1) : d200902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26060, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26060, d200902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26061 q = 1) (hb : d198467 q = 1) : d200903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26061, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26061, d200903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26062 q = 1) (hb : d198467 q = 1) : d200904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26062, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26062, d200904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26063 q = 1) (hb : d198467 q = 1) : d200905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26063, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26063, d200905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26064 q = 1) (hb : d198467 q = 1) : d200906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26064, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26064, d200906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61488 (p : Pattern) (ha : d25745 p = 1) (hb : d198467 p = 1) : d200729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d198467 q = 1) : d200702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d200702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d198467 q = 1) : d200728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d200728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25745 q = 1) (hb : d198467 q = 1) : d200729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25745, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25745, d200729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61489 (p : Pattern) (ha : d25747 p = 1) (hb : d198467 p = 1) : d200731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d198467 q = 1) : d200706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d200706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d198467 q = 1) : d200730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d200730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25747 q = 1) (hb : d198467 q = 1) : d200731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25747, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25747, d200731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61490 (p : Pattern) (ha : d25754 p = 1) (hb : d198467 p = 1) : d200738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d198467 q = 1) : d200701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d200701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d198467 q = 1) : d200736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d200736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d198467 q = 1) : d200737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d200737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25754 q = 1) (hb : d198467 q = 1) : d200738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25754, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25754, d200738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61491 (p : Pattern) (ha : d25757 p = 1) (hb : d198467 p = 1) : d200741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d198467 q = 1) : d200699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61474 q ha hb
    | true =>
      simp only [d25715, d200699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d198467 q = 1) : d200700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d200700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d198467 q = 1) : d200705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d200705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d198467 q = 1) : d200739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d200739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d198467 q = 1) : d200740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d200740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25757 q = 1) (hb : d198467 q = 1) : d200741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25757, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25757, d200741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro61492 (p : Pattern) (ha : d25770 p = 1) (hb : d198467 p = 1) : d200745 p = 1 := by
  have h0 (q : Pattern) (ha : d25763 q = 1) (hb : d152852 q = 1) : d25763 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25770 q = 1) (hb : d198467 q = 1) : d200745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25770, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25770, d198467, d200745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61493 (p : Pattern) (ha : d25775 p = 1) (hb : d198467 p = 1) : d200517 p = 1 := by
  have h0 (q : Pattern) (ha : d25431 q = 1) (hb : d152852 q = 1) : d25431 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25775 q = 1) (hb : d198467 q = 1) : d200517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25775, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25775, d198467, d200517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61494 (p : Pattern) (ha : d25783 p = 1) (hb : d198467 p = 1) : d200751 p = 1 := by
  have h0 (q : Pattern) (ha : d25782 q = 1) (hb : d152852 q = 1) : d25782 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25783 q = 1) (hb : d198467 q = 1) : d200751 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25783, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25783, d198467, d200751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro61495 (p : Pattern) (ha : d25789 p = 1) (hb : d198467 p = 1) : d200757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25771 q = 1) (hb : d198467 q = 1) : d200746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61492 q ha hb
    | true =>
      simp only [d25771, d200746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25772 q = 1) (hb : d198467 q = 1) : d200747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25772, d200747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25773 q = 1) (hb : d198467 q = 1) : d200748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25773, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25773, d200748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25774 q = 1) (hb : d198467 q = 1) : d200749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25774, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25774, d200749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25776 q = 1) (hb : d198467 q = 1) : d200518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61493 q ha hb
    | true =>
      simp only [d25776, d200518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25777 q = 1) (hb : d198467 q = 1) : d200519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25777, d200519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25778 q = 1) (hb : d198467 q = 1) : d200520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25778, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25778, d200520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25779 q = 1) (hb : d198467 q = 1) : d200521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25779, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25779, d200521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25780 q = 1) (hb : d198467 q = 1) : d200750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25780, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25780, d200750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25784 q = 1) (hb : d198467 q = 1) : d200752 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25784, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61494 q ha hb
    | true =>
      simp only [d25784, d200752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25785 q = 1) (hb : d198467 q = 1) : d200753 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25785, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25785, d200753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25786 q = 1) (hb : d198467 q = 1) : d200754 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25786, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25786, d200754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25787 q = 1) (hb : d198467 q = 1) : d200755 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25787, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25787, d200755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25452 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
    | true =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25453 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25454 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25455 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25788 q = 1) (hb : d198467 q = 1) : d200756 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25788, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25788, d200756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25789 q = 1) (hb : d198467 q = 1) : d200757 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25789, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25789, d200757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro61496 (p : Pattern) (ha : d25793 p = 1) (hb : d198467 p = 1) : d200761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25452 q = 1) (hb : d198467 q = 1) : d200524 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61446 q ha hb
    | true =>
      simp only [d25452, d200524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25453 q = 1) (hb : d198467 q = 1) : d200525 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25453, d200525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25454 q = 1) (hb : d198467 q = 1) : d200526 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d200526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25455 q = 1) (hb : d198467 q = 1) : d200527 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25455, d200527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25694 q = 1) (hb : d198467 q = 1) : d25694 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25695 q = 1) (hb : d198467 q = 1) : d200682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25695, d200682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25698 q = 1) (hb : d198467 q = 1) : d25698 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25793 q = 1) (hb : d198467 q = 1) : d200761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25793, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25793, d200761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61497 (p : Pattern) (ha : d25799 p = 1) (hb : d198467 p = 1) : d200767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25790 q = 1) (hb : d198467 q = 1) : d200758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25790, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61495 q ha hb
    | true =>
      simp only [d25790, d200758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61471 q ha hb
  have h2 (q : Pattern) (ha : d25791 q = 1) (hb : d198467 q = 1) : d200759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25791, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25791, d200759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25792 q = 1) (hb : d198467 q = 1) : d200760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25792, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25792, d200760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25794 q = 1) (hb : d198467 q = 1) : d200762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25794, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61471 q ha hb
    | true =>
      simp only [d25794, d200762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61496 q ha hb
  have h5 (q : Pattern) (ha : d25795 q = 1) (hb : d198467 q = 1) : d200763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25795, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25795, d200763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25796 q = 1) (hb : d198467 q = 1) : d200764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25796, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25796, d200764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25797 q = 1) (hb : d198467 q = 1) : d200765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25797, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25797, d200765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25700 q = 1) (hb : d198467 q = 1) : d200685 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61471 q ha hb
    | true =>
      simp only [d25700, d200685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61472 q ha hb
  have h9 (q : Pattern) (ha : d25701 q = 1) (hb : d198467 q = 1) : d200686 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d200686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25702 q = 1) (hb : d198467 q = 1) : d200687 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d200687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25703 q = 1) (hb : d198467 q = 1) : d25703 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25704 q = 1) (hb : d198467 q = 1) : d200688 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61472 q ha hb
    | true =>
      simp only [d25704, d200688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25705 q = 1) (hb : d198467 q = 1) : d200689 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d200689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25706 q = 1) (hb : d198467 q = 1) : d200690 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d200690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25707 q = 1) (hb : d198467 q = 1) : d200691 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25707, d200691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25798 q = 1) (hb : d198467 q = 1) : d200766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25798, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25798, d200766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25799 q = 1) (hb : d198467 q = 1) : d200767 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25799, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25799, d200767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro61498 (p : Pattern) (ha : d25805 p = 1) (hb : d198467 p = 1) : d200773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d198467 q = 1) : d200768 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61497 q ha hb
    | true =>
      simp only [d25800, d200768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d198467 q = 1) : d200769 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d200769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d198467 q = 1) : d200770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d200770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d198467 q = 1) : d200771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d200771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d198467 q = 1) : d200772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d200772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25805 q = 1) (hb : d198467 q = 1) : d200773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25805, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25805, d200773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro61499 (p : Pattern) (ha : d25875 p = 1) (hb : d198467 p = 1) : d200779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d198467 q = 1) : d200695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61473 q ha hb
    | true =>
      simp only [d25711, d200695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d198467 q = 1) : d200696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d200696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d198467 q = 1) : d200776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d200776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d198467 q = 1) : d200777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d200777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d198467 q = 1) : d200778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d200778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25875 q = 1) (hb : d198467 q = 1) : d200779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25875, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25875, d200779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
